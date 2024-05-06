%{
	#include<bits/stdc++.h>
	#include<string.h>
    #include<stdlib.h>
    #include<ctype.h>
    #include"lex.yy.c"
	typedef long long ll;
	using namespace std;
	int yylex();
	void yyerror(char *s);
	
void insert_type();
    int search(char *);
	void insert_type();
	void print_tree(struct node *);
	void print_inorder(struct node *);
    void check_declaration(char *);
	void check_return_type(char *);
	int check_types(char *, char *);
	char *get_type(char *);
	struct node* mknode(struct node *left, struct node *right, char *token);

    struct dataType {
        char * id_name;
        char * data_type;
        char * type;
        int line_no;
	} symbol_table[40];

    int count=0;
    int q;
	char type[10];
    extern int countn;
	struct node *head;
	int sem_errors=0;
	int label=0;
	char buff[100];
	char errors[10][100];
	char reserved[10][10] = {"int", "float", "char", "void", "if", "else", "for", "main", "return", "include"};

	struct node { 
		struct node *left; 
		struct node *right; 
		char *token; 
	};


	//for 3addr
	int tempcount=0;
	int getTemp();
	typedef struct node
	{
		string  addr, array;
		pair<string,vector<ll> > type;
		vector<ll> trueList,falseList,nextList;
		int instNum;
	}NODE;

	NODE* makeNode()
	{
		NODE *temp=new NODE();
		ostringstream ss;
		ss<<"t"<<getTemp();
		temp->addr=ss.str();
		ss.str("");
		temp->array="";
		return temp;
	}
	NODE* makeNode(string *x)
	{
		NODE *temp=new NODE();
		temp->addr=*x;
		temp->array="";
		return temp;
	}

	//for symbol table
	deque<string> s;
	deque<int> vars;
	deque<int> blocks;
	int blocknum=-1,varnum=0;
	string currType;
	map<ll,map<string,pair<pair<string,vector<ll> >,string> > > table;//blockno,varname,type,dimensions,value
	map<string,ll> width;
	ll getWidth(pair<string,vector<ll> > type);
	string to_string(ll val);
	ll to_int(string val);
	void insertID(int bno,string varname);
	void printTable();

	// for backpatch
	int instCounter=0;
	map<ll,string> instList;
	int nextInst();
	vector<ll> merge(vector<ll> a,vector<ll> b);
	void backpatch(vector<ll> list,int num);
	void displayInst();

	//for Control Flow Graph
	map<ll,vector<string> > basicBlock;
	set<ll> leaders;
	vector<vector<ll> > bbgraph;
	void genBasicBlock();
	void findLeaders();

%}

%union{
	typedef struct node NODE;
	string *str;
	NODE *node;

	struct var_name { 
			char name[100]; 
			struct node* nd;
		} nd_obj;

		struct var_name2 { 
			char name[100]; 
			struct node* nd;
			char type[5];
		} nd_obj2; 

}

%token <str> KEY AND OR NOT RELOP ID VAL SC CM PL MI MUL DIV POW OP CL AO AC EQ BO BC UNR TRUE FALSE IF ELSE WHILE
%type <node> bool bb m n e t f g l r a if ifelse while stmt stmt_list block decl function
%type <str>  d id arr ss 
%token VOID 
%token <nd_obj> CHARACTER PRINTFF SCANFF INT FLOAT CHAR FOR IF ELSE TRUE FALSE NUMBER FLOAT_NUM ID LE GE EQ NE GT LT AND OR STR ADD MULTIPLY DIVIDE SUBTRACT UNARY INCLUDE RETURN 
%type <nd_obj> headers main body return datatype statement arithmetic relop program else condition
%type <nd_obj2> init value expression

%%

ss:		
		{
			blocknum++;
			blocks.push_back(blocknum);
			vars.push_back(varnum);
			varnum=0;
		}
		stmt_list {};


datatype: int { insert_type(); }
| float { insert_type(); }
| char { insert_type(); }
| void { insert_type(); }
;

stmt:	if {($$)=new NODE();($$)->nextList=($1)->nextList;} |
		 ifelse {($$)=new NODE();($$)->nextList=($1)->nextList;} |
		  while {($$)=new NODE();($$)->nextList=($1)->nextList;} |
		   block {($$)=new NODE();($$)->nextList=($1)->nextList;} |
		    a {($$)=new NODE();($$)->nextList=($1)->nextList;}|
		     decl{($$)=new NODE();($$)->nextList=($1)->nextList;} |
			 function {($$)=new NODE();($$)->nextList=($1)->nextList;};

if:		IF OP bool CL m stmt {
								($$)=new NODE();
								backpatch(($3)->trueList,($5)->instNum);
								($$)->nextList=merge(($3)->falseList,($6)->nextList);
							};
ifelse: IF OP bool CL m stmt ELSE n m stmt {
											($$)=new NODE();
											backpatch(($3)->trueList,($5)->instNum);
											backpatch(($3)->falseList,($9)->instNum);
											($$)->nextList=merge(($6)->nextList,($8)->nextList);
											($$)->nextList=merge(($$)->nextList,($10)->nextList);
										};
while:	WHILE m OP bool CL m stmt {
									($$)=new NODE();
									backpatch(($4)->trueList,($6)->instNum);
									backpatch(($7)->nextList,($2)->instNum);
									instList[nextInst()]="goto "+to_string(($2)->instNum);
									($$)->nextList=($4)->falseList;
								};
block: BO	{
			blocknum++;
			blocks.push_back(blocknum);
			for(int i=0;i<s.size();i++)
			{
				insertID(blocknum,s[i]);
			}
			vars.push_back(varnum);
			varnum=0;
		} 
		stmt_list BC 
		{
			blocks.pop_back();
			for(int i=0;i<varnum;i++)
				s.pop_back();
			varnum=vars.back();
			vars.pop_back();	
			($$)=new NODE();
			($$)->nextList=($3)->nextList;
		};
stmt_list: stmt_list m stmt {
								($$)=new NODE();
								backpatch(($1)->nextList,($2)->instNum);
								($$)->nextList=($3)->nextList;
							} |
			 stmt {($$)->nextList=($1)->nextList;} | {};
decl: KEY id {
				varnum++;s.push_back(*($1)+" "+*($2));
				insertID(blocks.back(),*($1)+" "+*($2));
				currType=*($1);
				{ check_declaration($1.name); } '=' expression {
	$1.nd = mknode(NULL, NULL, $1.name); 
	char *id_type = get_type($1.name); 
	if(strcmp(id_type, $4.type)) {
		if(!strcmp(id_type, "int")) {
			if(!strcmp($4.type, "float")){
				struct node *temp = mknode(NULL, $4.nd, "floattoint");
				$$.nd = mknode($1.nd, temp, "="); 
			}
			else{
				struct node *temp = mknode(NULL, $4.nd, "chartoint");
				$$.nd = mknode($1.nd, temp, "="); 
			}
			
		}
		else if(!strcmp(id_type, "float")) {
			if(!strcmp($4.type, "int")){
				struct node *temp = mknode(NULL, $4.nd, "inttofloat");
				$$.nd = mknode($1.nd, temp, "="); 
			}
			else{
				struct node *temp = mknode(NULL, $4.nd, "chartofloat");
				$$.nd = mknode($1.nd, temp, "="); 
			}
			
		}
		else{
			if(!strcmp($4.type, "int")){
				struct node *temp = mknode(NULL, $4.nd, "inttochar");
				$$.nd = mknode($1.nd, temp, "="); 
			}
			else{
				struct node *temp = mknode(NULL, $4.nd, "floattochar");
				$$.nd = mknode($1.nd, temp, "="); 
			}
		}
	}
	else {
		$$.nd = mknode($1.nd, $4.nd, "="); 
	}

			} d SC {($$)=new NODE();}
| ID { check_declaration($1.name); } relop expression { $1.nd = mknode(NULL, NULL, $1.name); $$.nd = mknode($1.nd, $4.nd, $3.name); }
| ID { check_declaration($1.name); } UNARY { 
	$1.nd = mknode(NULL, NULL, $1.name); 
	$3.nd = mknode(NULL, NULL, $3.name); 
	$$.nd = mknode($1.nd, $3.nd, "ITERATOR");  
}
| UNARY ID { 
	check_declaration($2.name); 
	$1.nd = mknode(NULL, NULL, $1.name); 
	$2.nd = mknode(NULL, NULL, $2.name); 
	$$.nd = mknode($1.nd, $2.nd, "ITERATOR"); 
}
;
		

function: KEY ID '(' id {
				varnum++;s.push_back(*($1)+" "+*($2));
				insertID(blocks.back(),*($1)+" "+*($2));
				currType=*($1);
			} ')' '{' stmt '}'; 

id:	ID arr{($$)=new string(*($1)+*($2));} | ID arr EQ VAL {($$)=new string(*($1)+*($2)+*($3)+*($4));}{ 
	$2.nd = mknode(NULL, NULL, $2.name); 
	int t = check_types($1.name, $4.type); 
	if(t>0) { 
		if(t == 1) {
			struct node *temp = mknode(NULL, $4.nd, "floattoint"); 
			$$.nd = mknode($2.nd, temp, "declaration"); 
		} 
		else if(t == 2) { 
			struct node *temp = mknode(NULL, $4.nd, "inttofloat"); 
			$$.nd = mknode($2.nd, temp, "declaration"); 
		} 
		else if(t == 3) { 
			struct node *temp = mknode(NULL, $4.nd, "chartoint"); 
			$$.nd = mknode($2.nd, temp, "declaration"); 
		} 
		else if(t == 4) { 
			struct node *temp = mknode(NULL, $4.nd, "inttochar"); 
			$$.nd = mknode($2.nd, temp, "declaration"); 
		} 
		else if(t == 5) { 
			struct node *temp = mknode(NULL, $4.nd, "chartofloat"); 
			$$.nd = mknode($2.nd, temp, "declaration"); 
		} 
		else{
			struct node *temp = mknode(NULL, $4.nd, "floattochar"); 
			$$.nd = mknode($2.nd, temp, "declaration"); 
		}
	} 
	else { 
		$$.nd = mknode($2.nd, $4.nd, "declaration"); 
	} 
};

arr:	AO VAL AC arr {($$)=new string(*($1)+*($2)+*($3)+*($4));}| {($$)=new string("");};

d: CM id {
			varnum++;s.push_back(currType+" "+*($2));
			insertID(blocks.back(),currType+" "+*($2));
		} d | {};

a:	l EQ r SC {instList[nextInst()]=($1)->array+"["+($1)->addr+"] = "+($3)->addr;	} |
	  	ID EQ r SC 	{
	  					if(table[blocks.back()].find(*($1))==table[blocks.back()].end())
						{
							yyerror("variable not declared");
						}
	  					instList[nextInst()]=*($1)+" = "+($3)->addr;
	  					($$)=new NODE();
	  				} ;
l: 	 ID AO e AC 
				{
					($$)=makeNode();
					($$)->array=*($1);
					if(table[blocks.back()].find(*($1))==table[blocks.back()].end())
					{
						yyerror("variable not declared");
					}
					($$)->type=table[blocks.back()][*($1)].first;
					instList[nextInst()]=($$)->addr+" = "+($3)->addr+" * "+to_string((int)getWidth(($$)->type));
				} |
		 l AO e AC
		 		{
		 			NODE *myTemp=makeNode();
		 			($$)=makeNode();
		 			($$)->array=($1)->array;
		 			($$)->type=($1)->type;
		 			($$)->type.second.erase(($$)->type.second.begin());
		 			instList[nextInst()]=myTemp->addr + " = "+($3)->addr +" * "+to_string((int)getWidth(($$)->type));
		 			instList[nextInst()]=($$)->addr+" = "+($1)->addr+ " + " + myTemp->addr;
		 		}
r : e 	{($$)=($1);};

bool:	bool OR m bb 	{
					($$)=new NODE();
					backpatch(($1)->falseList,($3)->instNum);
					($$)->trueList=merge(($1)->trueList,($4)->trueList);
					($$)->falseList=($4)->falseList;
				} |
	 bool AND m bb	{
	 				($$)=new NODE();
	 				backpatch(($1)->trueList,($3)->instNum);
	 				($$)->trueList=($4)->trueList;
	 				($$)->falseList=merge(($1)->falseList,($4)->falseList);
				} |
		 bb {($$)=new NODE();($$)->trueList=($1)->trueList;($$)->falseList=($1)->falseList;};

bb:	  NOT bb {($$)=new NODE();($$)->trueList=($2)->falseList;($$)->falseList=($2)->trueList;} |
	   OP bool CL {($$)=new NODE();($$)->trueList=($2)->trueList;($$)->falseList=($2)->falseList;} |
	    e RELOP e 	{
	    				($$)=new NODE();
	    				($$)->trueList.push_back(nextInst());
	    				instList[($$)->trueList.back()]="if "+($1)->addr+" "+*($2)+" "+($3)->addr+" goto";
	    				($$)->falseList.push_back(nextInst());
	    				instList[($$)->falseList.back()]="goto";
	    			} |
	     TRUE {($$)=new NODE();($$)->trueList.push_back(nextInst());instList[($$)->trueList.back()]="goto";} |
	      FALSE {($$)=new NODE();($$)->falseList.push_back(nextInst());instList[($$)->falseList.back()]="goto";};

m:	{($$)=new NODE();($$)=new NODE();($$)->instNum=instCounter;};
n:	{($$)=new NODE();($$)->nextList.push_back(nextInst());instList[($$)->nextList.back()]="goto";};

e : e arithmetic t {($$)=makeNode();instList[nextInst()]=($$)->addr+" = "+($1)->addr+" + "+($3)->addr;}|
	 e arithmetic t {($$)=makeNode();instList[nextInst()]=($$)->addr+" = "+($1)->addr+" - "+($3)->addr;}|
	  t {($$)=($1);} |
	   l {($$)=makeNode();instList[nextInst()]=($$)->addr+" = "+($1)->array+"["+($1)->addr+"]";}{ 
	if(!strcmp($1.type, $3.type)) {
		sprintf($$.type, 
		$1.type);
		$$.nd = mknode($1.nd, $3.nd, $2.name); 
	}
	else {
		if(!strcmp($1.type, "int") && !strcmp($3.type, "float")) {
			struct node *temp = mknode(NULL, $1.nd, "inttofloat");
			sprintf($$.type, $3.type);
			$$.nd = mknode(temp, $3.nd, $2.name);
		}
		else if(!strcmp($1.type, "float") && !strcmp($3.type, "int")) {
			struct node *temp = mknode(NULL, $3.nd, "inttofloat");
			sprintf($$.type, $1.type);
			$$.nd = mknode($1.nd, temp, $2.name);
		}
		else if(!strcmp($1.type, "int") && !strcmp($3.type, "char")) {
			struct node *temp = mknode(NULL, $3.nd, "chartoint");
			sprintf($$.type, $1.type);
			$$.nd = mknode($1.nd, temp, $2.name);
		}
		else if(!strcmp($1.type, "char") && !strcmp($3.type, "int")) {
			struct node *temp = mknode(NULL, $1.nd, "chartoint");
			sprintf($$.type, $3.type);
			$$.nd = mknode(temp, $3.nd, $2.name);
		}
		else if(!strcmp($1.type, "float") && !strcmp($3.type, "char")) {
			struct node *temp = mknode(NULL, $3.nd, "chartofloat");
			sprintf($$.type, $1.type);
			$$.nd = mknode($1.nd, temp, $2.name);
		}
		else {
			struct node *temp = mknode(NULL, $1.nd, "chartofloat");
			sprintf($$.type, $3.type);
			$$.nd = mknode(temp, $3.nd, $2.name);
		}
	}
}
| value { strcpy($$.name, $1.name); sprintf($$.type, $1.type); $$.nd = $1.nd; }
;
;

t : t arithmetic f {($$)=makeNode();instList[nextInst()]=($$)->addr+" = "+($1)->addr+" * "+($3)->addr;}|
	 t arithmetic f {($$)=makeNode();instList[nextInst()]=($$)->addr+" = "+($1)->addr+" / "+($3)->addr;}|
	  f {($$)=($1);}{ 
	if(!strcmp($1.type, $3.type)) {
		sprintf($$.type, 
		$1.type);
		$$.nd = mknode($1.nd, $3.nd, $2.name); 
	}
	else {
		if(!strcmp($1.type, "int") && !strcmp($3.type, "float")) {
			struct node *temp = mknode(NULL, $1.nd, "inttofloat");
			sprintf($$.type, $3.type);
			$$.nd = mknode(temp, $3.nd, $2.name);
		}
		else if(!strcmp($1.type, "float") && !strcmp($3.type, "int")) {
			struct node *temp = mknode(NULL, $3.nd, "inttofloat");
			sprintf($$.type, $1.type);
			$$.nd = mknode($1.nd, temp, $2.name);
		}
		else if(!strcmp($1.type, "int") && !strcmp($3.type, "char")) {
			struct node *temp = mknode(NULL, $3.nd, "chartoint");
			sprintf($$.type, $1.type);
			$$.nd = mknode($1.nd, temp, $2.name);
		}
		else if(!strcmp($1.type, "char") && !strcmp($3.type, "int")) {
			struct node *temp = mknode(NULL, $1.nd, "chartoint");
			sprintf($$.type, $3.type);
			$$.nd = mknode(temp, $3.nd, $2.name);
		}
		else if(!strcmp($1.type, "float") && !strcmp($3.type, "char")) {
			struct node *temp = mknode(NULL, $3.nd, "chartofloat");
			sprintf($$.type, $1.type);
			$$.nd = mknode($1.nd, temp, $2.name);
		}
		else {
			struct node *temp = mknode(NULL, $1.nd, "chartofloat");
			sprintf($$.type, $3.type);
			$$.nd = mknode(temp, $3.nd, $2.name);
		}
	}
}
| value { strcpy($$.name, $1.name); sprintf($$.type, $1.type); $$.nd = $1.nd; }
;


arithmetic: PL
| MI 
| MUL
| DIV
;

f : g POW f {($$)=makeNode();instList[nextInst()]=($$)->addr+" = "+($1)->addr+" ^ "+($3)->addr;}|
	 g {($$)=($1);};

g : OP e CL {($$)=($2);}|
	 ID {
	 		if(table[blocks.back()].find(*($1))==table[blocks.back()].end())
			{
				yyerror("variable not declared");
			}
			($$)=makeNode(($1));
		} |
	 l {
	 		($$)=makeNode();instList[nextInst()]=($$)->addr+" = "+($1)->array+"["+($1)->addr+"]";
	 	} |
	  VAL {($$)=makeNode($1);} |
	   MI g {($$)=makeNode();instList[nextInst()]=($$)->addr+" = - "+($2)->addr;};

%%
//for DAG
bool isInt(string s)
{
	bool flag=true;
	for(ll i=0;i<s.length();i++)
	{
		if(s[i]<'0' || s[i]>'9')
			flag=false;
	}
	return flag;
}
typedef struct dNode
{
	string op,name;
	vector<string> resVars;
	bool isGenerated;
	vector<struct dNode*> children;
}dagNode;

vector<vector<dagNode*> > dagBlock;
map<string,ll> dagVarCount;

dagNode* getDAGNode(string name, string op)
{
	dagNode *x=new dagNode();
	x->op=op;
	x->resVars.push_back(name+"_"+to_string((int)dagVarCount[name]));
	dagVarCount[name]++;
	x->isGenerated=false;
	return x;
}
dagNode* getDAGNode(string name)
{
	dagNode *x=new dagNode();
	if(isInt(name))
	{
		x->name=name;
	}
	else
		x->name=name+"_"+to_string((int)dagVarCount[name]);
	x->isGenerated=false;
	dagVarCount[name]++;
	return x;
}

string getVarName(dagNode *curr)
{
	if(curr->name!="")
		return curr->name;
	if(curr->resVars.size()>0)
		return curr->resVars.front();
	return "<not found>";
}
string getVarName(string var)
{
	return var.substr(0,var.rfind("_"));
}
void dfsDAG(dagNode *curr,string tab="\t")
{
	if(curr->op!="")
		cout<<tab<<"OP: "<<curr->op<<endl;
	if(curr->name!="")
		cout<<tab<<"NAME: "<<curr->name<<endl;
	if(curr->resVars.size()>0)
	{
		cout<<tab<<"ResVars: ";
		for(ll i=0;i<curr->resVars.size();i++)
		{
			cout<<curr->resVars[i]<<" ";
		}
		cout<<endl;
	}	
	for(ll i=0;i<curr->children.size();i++)
	{
		cout<<tab<<"child "<<(i+1)<<":"<<endl;
		dfsDAG(curr->children[i],tab+"\t");
	}
}
void displayDAG()
{
	cout<<"DAG:"<<endl;
	for(ll i=0;i<dagBlock.size();i++)
	{
		cout<<"Block "<<i<<":"<<endl;
		for(ll j=0;j<dagBlock[i].size();j++)
		{
			dfsDAG(dagBlock[i][j]);
			cout<<endl;
		}
	}
}
bool findDagNode(map<string,dagNode*> dagMap,dagNode *res,string op1,string op,string op2="")
{
	for(map<string,dagNode*>::iterator it=dagMap.begin();it!=dagMap.end();it++)
	{
		dagNode *curr=it->second;
		if(curr->op==op)
		{
			if(curr->children.size()==2 && op2!="")
			{
				bool one=(getVarName(curr->children[0]->name)==op1),two=(getVarName(curr->children[1]->name)==op2);
				for(int i=0;i<curr->children[0]->resVars.size();i++)
				{
					if(op1==getVarName(curr->children[0]->resVars[i]))
						one=true;
				}
				for(int i=0;i<curr->children[1]->resVars.size();i++)
				{
					if(op2==getVarName(curr->children[1]->resVars[i]))
						two=true;
				}
				if(one && two)
				{
					res=curr;
					return true;
				}
			}
			if(curr->children.size()==1)
			{
				bool one=(getVarName(curr->children[0]->name)==op1);
				for(int i=0;i<curr->children[0]->resVars.size();i++)
				{
					if(op1==getVarName(curr->children[0]->resVars[i]))
						one=true;
				}
				if(one)
				{
					res=curr;
					return true;
				}
			}
		}
	}
	return false;
}
void genDAG(ll bno)
{
	vector<string> inst=basicBlock[bno];
	map<string,dagNode*> dagMap;
	for(ll i=0;i<inst.size();i++)
	{
		istringstream ss(inst[i]);
		string temp;
		vector<string> splits;
		while(ss>>temp)
		{
			splits.push_back(temp);
		}
		if(splits.size()>0 && splits[0]=="if" || splits[0]=="goto")
			continue;
		if(splits.size()==5)
		{
			dagNode *op1,*op2,*res;
			if(findDagNode(dagMap,res,splits[2],splits[3],splits[4]))
			{
				res->resVars.push_back(splits[0]+"_"+to_string((int)dagVarCount[splits[0]]));
				dagMap[splits[0]]=res;
				continue;
			}
			if(dagMap.find(splits[2])!=dagMap.end())
				op1=dagMap[splits[2]];
			else
				op1=getDAGNode(splits[2]);
			if(dagMap.find(splits[4])!=dagMap.end())
				op2=dagMap[splits[4]];
			else
				op2=getDAGNode(splits[4]);
			res=getDAGNode(splits[0],splits[3]);
			res->children.push_back(op1);
			res->children.push_back(op2);
			for(ll j=0;j<dagBlock[bno].size();j++)
			{
				if(dagBlock[bno][j]==op1 || dagBlock[bno][j]==op2)
				{
					dagBlock[bno].erase(dagBlock[bno].begin()+j);
					j--;
				}
			}
			dagBlock[bno].push_back(res);
			dagMap[splits[2]]=op1;
			dagMap[splits[4]]=op2;
			dagMap[splits[0]]=res;
		}
		else if(splits.size()==3)
		{
			dagNode *op1,*res;
			if(splits[2].find("[")!=-1)
			{
				dagNode *op2;
				ll ind=splits[2].find("[");
				string base=splits[2].substr(0,ind),offset=splits[2].substr(ind+1,splits[2].find("]")-ind-1);
				if(dagMap.find(base)!=dagMap.end())
					op1=dagMap[base];
				else
					op1=getDAGNode(base);
				if(dagMap.find(offset)!=dagMap.end())
					op2=dagMap[offset];
				else
					op2=getDAGNode(offset);
				res=getDAGNode(splits[0],"=[]");
				res->children.push_back(op1);
				res->children.push_back(op2);
				for(ll j=0;j<dagBlock[bno].size();j++)
				{
					if(dagBlock[bno][j]==op1 || dagBlock[bno][j]==op2)
					{
						dagBlock[bno].erase(dagBlock[bno].begin()+j);
						j--;
					}
				}
				dagBlock[bno].push_back(res);
				dagMap[base]=op1;
				dagMap[offset]=op2;
				dagMap[splits[0]]=res;
				continue;
			}
			if(splits[0].find("[")!=-1)
			{
				dagNode *op2,*op3;
				ll ind=splits[0].find("[");
				string base=splits[0].substr(0,ind),offset=splits[0].substr(ind+1,splits[0].find("]")-ind-1);
				if(dagMap.find(base)!=dagMap.end())
					op1=dagMap[base];
				else
					op1=getDAGNode(base);
				if(dagMap.find(offset)!=dagMap.end())
					op2=dagMap[offset];
				else
					op2=getDAGNode(offset);
				if(dagMap.find(splits[2])!=dagMap.end())
					op3=dagMap[splits[2]];
				else
					op3=getDAGNode(splits[2]);
				res=getDAGNode(base,"[]=");
				res->children.push_back(op1);
				res->children.push_back(op2);
				res->children.push_back(op3);
				for(ll j=0;j<dagBlock[bno].size();j++)
				{
					if(dagBlock[bno][j]==op1 || dagBlock[bno][j]==op2 || dagBlock[bno][j]==op3)
					{
						dagBlock[bno].erase(dagBlock[bno].begin()+j);
						j--;
					}
				}
				dagBlock[bno].push_back(res);
				dagMap[base]=op1;
				dagMap[offset]=op2;
				dagMap[splits[2]]=op3;
				continue;
			}
			if(findDagNode(dagMap,res,splits[2],splits[1]))
			{
				res->resVars.push_back(splits[0]+"_"+to_string((int)dagVarCount[splits[0]]));
				dagMap[splits[0]]=res;
				continue;
			}
			if(dagMap.find(splits[2])!=dagMap.end())
			{
				op1=dagMap[splits[2]];
				op1->resVars.push_back(splits[0]+"_"+to_string((int)dagVarCount[splits[0]]));
				dagVarCount[splits[0]]++;
				dagMap[splits[0]]=op1;
			}
			else
			{
				op1=getDAGNode(splits[2]);
				op1->resVars.push_back(splits[0]+"_"+to_string((int)dagVarCount[splits[0]]));
				dagVarCount[splits[0]]++;
				dagBlock[bno].push_back(op1);
				dagMap[splits[0]]=op1;
				dagMap[splits[2]]=op1;
			}
			
		}
	}
}


void dagToThreeAddr(dagNode *curr)
{
	if(curr->isGenerated)
	{
		return;
	}
	for(ll i=0;i<curr->children.size();i++)
	{
		dagToThreeAddr(curr->children[i]);
	}
	if(curr->children.size()<2)
		return;
	if(curr->children.size()==2)
	{
		cout<<curr->resVars.front()<<" = "<<getVarName(curr->children[0])<<" "<<curr->op<<" "<<getVarName(curr->children[1])<<endl;
	}
	curr->isGenerated=true;
}
void genThreeAddr()
{
	cout<<"New Three Address:"<<endl;
	for(ll i=0;i<dagBlock.size();i++)
	{
		cout<<"Block "<<i<<": "<<endl;
		for(ll j=0;j<dagBlock[i].size();j++)
		{
			dagToThreeAddr(dagBlock[i][j]);
		}
		cout<<endl;
	}
}
void genDAG()
{
	dagBlock.resize(basicBlock.size());
	for(ll i=0;i<dagBlock.size();i++)
		genDAG(i);
}
void genFlowGraph()
{
	bbgraph.resize(basicBlock.size());
	for(map<ll,vector<string> >::iterator it=basicBlock.begin();it!=basicBlock.end();it++)
	{
		ll ind=-1;
		string lastStmt=it->second.back();
		if((ind=lastStmt.rfind("goto"))!=-1)
		{
			bbgraph[it->first].push_back(to_int(lastStmt.substr(ind+5)));
			if(ind!=0 && it->first!=basicBlock.size()-1)
			{
				bbgraph[it->first].push_back(it->first+1);
			}
		}
		else
		{
			if(it->first!=basicBlock.size()-1)
				bbgraph[it->first].push_back(it->first+1);
		}
	}
}
void displayFlowGraph()
{
	cout<<"Flow Graph:"<<endl;
	for(ll i=0;i<bbgraph.size();i++)
	{
		cout<<i<<": ";
		for(ll j=0;j<bbgraph[i].size();j++)
		{
			cout<<bbgraph[i][j]<<" ";
		}
		cout<<endl;
	}
	cout<<endl;
}
void findLeaders()
{
	bool flag=true;
	for(map<ll,string>::iterator it=instList.begin();it!=instList.end();it++)
	{
		if(flag)
		{
			leaders.insert(it->first);
			int ind=it->second.rfind("goto");
			if(ind!=-1)
			{
				leaders.insert(to_int(it->second.substr(ind+5)));
				flag=true;
				continue;
			}
			flag=false;
		}
		int ind=it->second.rfind("goto");
		if(ind!=-1)
		{
			leaders.insert(to_int(it->second.substr(ind+5)));
			flag=true;
			continue;
		}
	}
}
void displayLeaders()
{
	cout<<"Leaders:"<<endl;
	for(set<ll>::iterator it=leaders.begin();it!=leaders.end();it++)
	{
		cout<<*it<<endl;
	}
}
void genBasicBlock()
{
	findLeaders();
	map<ll,ll> lineToBlock;
	ll bbno=-1;
	for(map<ll,string>::iterator it=instList.begin();it!=instList.end();it++)
	{
		if(leaders.find(it->first)!=leaders.end())
		{
			bbno++;
		}
		lineToBlock[it->first]=bbno;
	}
	bbno=-1;
	for(map<ll,string>::iterator it=instList.begin();it!=instList.end();it++)
	{
		if(leaders.find(it->first)!=leaders.end())
		{
			bbno++;
		}
		int ind=-1;
		string bbinst=it->second;
		if((ind=it->second.rfind("goto"))!=-1)
		{
			bbinst=it->second.substr(0,ind+5) + to_string((int)lineToBlock[to_int(it->second.substr(ind+5))]);
		}
		basicBlock[bbno].push_back(bbinst);
	}
}
void displayBasicBlocks()
{
	cout<<"Basic Blocks:"<<endl;
	for(map<ll,vector<string> >::iterator it=basicBlock.begin();it!=basicBlock.end();it++)
	{
		cout<<"Block "<<it->first<<":"<<endl;
		for(ll i=0;i<it->second.size();i++)
		{
			cout<<"\t"<<it->second[i]<<endl;
		}
		cout<<endl;
	}
}
void displayInst()
{
	cout<<"Three Address Statements:"<<endl;
	for(map<ll,string>::iterator it=instList.begin();it!=instList.end();it++)
	{
		cout<<it->first<<" "<<it->second<<endl;
	}
	cout<<endl;
}

int getTemp()
{
	return tempcount++;
}
int nextInst()
{
	return instCounter++;
}
vector<ll> merge(vector<ll> a,vector<ll> b)
{
	a.insert(a.end(),b.begin(),b.end());
	return a;
}
void backpatch(vector<ll> list,int num)
{
	for(ll i=0;i<list.size();i++)
	{
		if(instList[list[i]].find("goto")==instList[list[i]].length()-4)
		{
			instList[list[i]]+=" "+to_string(num);
		}
	}
}
void insertID(int bno,string varname)
{
	string type,value;
	int ind=varname.find(" ");
	if(ind!=-1)
	{
		type=varname.substr(0,ind);
		varname=varname.substr(ind+1);
	}
	ind=varname.find("=");
	value="";
	if(ind!=-1)
	{
		value=varname.substr(ind+1);
		varname=varname.substr(0,ind);
	}
	ind=varname.find("[");
	vector<ll> dims;
	if(ind!=-1)
	{
		string indexes=varname.substr(ind);
		varname=varname.substr(0,ind);
		for(ll i=0;i<indexes.length();i++)
		{
			if(indexes[i]=='[' || indexes[i]==']')
				indexes[i]=' ';
		}
		istringstream in(indexes.c_str());
		int dim;
		while(in>>dim)
		{
			dims.push_back(dim);
		}
	}
	if(table[bno].find(varname)!=table[bno].end())
	{
		yyerror("variable already declared");
	}
	table[bno][varname]=make_pair(make_pair(type,dims),value);
}
ll getWidth(pair<string,vector<ll> > type)
{
	ll ans=width[type.first];
	for(ll i=1;i<type.second.size();i++)
	{
		ans=ans*type.second[i];
	}
	return ans;
}
void printTable()
{
	cout<<"Symbol Table:"<<endl;
	for(map<ll,map<string,pair<pair<string,vector<ll> >,string> > >::iterator it=table.begin();it!=table.end();it++)
	{
		cout<<"Block "<<it->first<<":"<<endl;
		for(map<string,pair<pair<string,vector<ll> >,string> >::iterator it2=it->second.begin();it2!=it->second.end();it2++)
		{
			cout<<it2->first<<" "<<it2->second.first.first<<" "<<it2->second.second;
			for(vector<ll>::iterator it3=it2->second.first.second.begin();it3!=it2->second.first.second.end();it3++)
				cout<<*it3<<' ';
			cout<<endl;
		}
		cout<<endl;
	}
}
void setWidths()
{
	width["int"]=4;
	width["float"]=4;
	width["char"]=1;
	width["double"]=8;
}
string to_string(ll val)
{
	ostringstream ss;
	ss<<val;
	return ss.str();
}
ll to_int(string val)
{
	istringstream ss(val);
	ll x;
	ss>>x;
	return x;
}
void readThreeAddress(int start=0)
{
	string inst;
	while(getline(cin,inst))
		instList[start++]=inst;
}
void yyerror(char* s)
{
	cout<<s<<endl;
	exit(0);
}
int main()
{
	setWidths();
	yyparse();
	printf("\n\n");
	printf("\t\t\t\t\t\t\t\t PHASE 1: LEXICAL ANALYSIS \n\n");
	printf("\nSYMBOL   DATATYPE   TYPE   LINE NUMBER \n");
	printf("_______________________________________\n\n");
	int i=0;
	for(i=0; i<count; i++) {
		printf("%s\t%s\t%s\t%d\t\n", symbol_table[i].id_name, symbol_table[i].data_type, symbol_table[i].type, symbol_table[i].line_no);
	}
	for(i=0;i<count;i++) {
		free(symbol_table[i].id_name);
		free(symbol_table[i].type);
	}
	printf("\n\n");
	printf("\t\t\t\t\t\t\t\t PHASE 2: SYNTAX ANALYSIS \n\n");
	print_tree(head); 
	printf("\n\n\n\n");
	printf("\t\t\t\t\t\t\t\t PHASE 3: SEMANTIC ANALYSIS \n\n");
	if(sem_errors>0) {
		printf("Semantic analysis completed with %d errors\n", sem_errors);
		for(int i=0; i<sem_errors; i++){
			printf("\t - %s", errors[i]);
		}
	} else {
		printf("Semantic analysis completed with no errors");
	}
	printf("\n\n");

	readThreeAddress();
	printTable();
	displayInst();
	genBasicBlock();
	displayBasicBlocks();
	genFlowGraph();
	displayFlowGraph();
	//comment the following if the code has control statements
	//use only with no control flows
	
	genDAG();
	displayDAG();
	genThreeAddr();
}

int search(char *type) {
	int i;
	for(i=count-1; i>=0; i--) {
		if(strcmp(symbol_table[i].id_name, type)==0) {
			return -1;
			break;
		}
	}
	return 0;
}

void check_declaration(char *c) {
    q = search(c);
    if(!q) {
        sprintf(errors[sem_errors], "Line %d: Variable \"%s\" not declared before usage!\n", countn+1, c);
		sem_errors++;
    }
}

void check_return_type(char *value) {
	char *main_datatype = get_type("main");
	char *return_datatype = get_type(value);
	if((!strcmp(main_datatype, "int") && !strcmp(return_datatype, "CONST")) || !strcmp(main_datatype, return_datatype)){
		return ;
	}
	else {
		sprintf(errors[sem_errors], "Line %d: Return type mismatch\n", countn+1);
		sem_errors++;
	}
}

int check_types(char *type1, char *type2){
	// declaration with no init
	if(!strcmp(type2, "null"))
		return -1;
	// both datatypes are same
	if(!strcmp(type1, type2))
		return 0;
	// both datatypes are different
	if(!strcmp(type1, "int") && !strcmp(type2, "float"))
		return 1;
	if(!strcmp(type1, "float") && !strcmp(type2, "int"))
		return 2;
	if(!strcmp(type1, "int") && !strcmp(type2, "char"))
		return 3;
	if(!strcmp(type1, "char") && !strcmp(type2, "int"))
		return 4;
	if(!strcmp(type1, "float") && !strcmp(type2, "char"))
		return 5;
	if(!strcmp(type1, "char") && !strcmp(type2, "float"))
		return 6;
}

char *get_type(char *var){
	for(int i=0; i<count; i++) {
		// Handle case of use before declaration
		if(!strcmp(symbol_table[i].id_name, var)) {
			return symbol_table[i].data_type;
		}
	}
}

void add(char c) {
	if(c == 'V'){
		for(int i=0; i<10; i++){
			if(!strcmp(reserved[i], strdup(yytext))){
        		sprintf(errors[sem_errors], "Line %d: Variable name \"%s\" is a reserved keyword!\n", countn+1, yytext);
				sem_errors++;
				return;
			}
		}
	}
    q=search(yytext);
	if(!q) {
		if(c == 'H') {
			symbol_table[count].id_name=strdup(yytext);
			symbol_table[count].data_type=strdup(type);
			symbol_table[count].line_no=countn;
			symbol_table[count].type=strdup("Header");
			count++;
		}
		else if(c == 'K') {
			symbol_table[count].id_name=strdup(yytext);
			symbol_table[count].data_type=strdup("N/A");
			symbol_table[count].line_no=countn;
			symbol_table[count].type=strdup("Keyword\t");
			count++;
		}
		else if(c == 'V') {
			symbol_table[count].id_name=strdup(yytext);
			symbol_table[count].data_type=strdup(type);
			symbol_table[count].line_no=countn;
			symbol_table[count].type=strdup("Variable");
			count++;
		}
		else if(c == 'C') {
			symbol_table[count].id_name=strdup(yytext);
			symbol_table[count].data_type=strdup("CONST");
			symbol_table[count].line_no=countn;
			symbol_table[count].type=strdup("Constant");
			count++;
		}
		else if(c == 'F') {
			symbol_table[count].id_name=strdup(yytext);
			symbol_table[count].data_type=strdup(type);
			symbol_table[count].line_no=countn;
			symbol_table[count].type=strdup("Function");
			count++;
		}
    }
    else if(c == 'V' && q) {
        sprintf(errors[sem_errors], "Line %d: Multiple declarations of \"%s\" not allowed!\n", countn+1, yytext);
		sem_errors++;
    }
}

struct node* mknode(struct node *left, struct node *right, char *token) {	
	struct node *newnode = (struct node *) malloc(sizeof(struct node));
	char *newstr = (char *) malloc(strlen(token)+1);
	strcpy(newstr, token);
	newnode->left = left;
	newnode->right = right;
	newnode->token = newstr;
	return(newnode);
}

void print_tree(struct node* t) {
	printf("\n\nInorder traversal of the Parse Tree is: \n\n");
	print_inorder(t);
}

void print_inorder(struct node *tree) {
	int i;
	if (tree->left) {
		print_inorder(tree->left);
	}
	printf("%s, ", tree->token);
	if (tree->right) {
		print_inorder(tree->right);
	}
}

void insert_type() {
	strcpy(type, yytext);
}

void yyerror(const char* msg) {
    fprintf(stderr, "%s\n", msg);
}

void check_array_arguments(char *var, int dimensions) {
   
    for (int i = 0; i < count; i++) {
        if (strcmp(symbol_table[i].id_name, var) == 0) {
            // Check if the variable is an array and if its dimensions match
            if (symbol_table[i].dimensions != dimensions) {
                // Dimensions mismatch, generate an error message
                sprintf(errors[sem_errors], "Line %d: Array argument \"%s\" dimensions mismatch!\n", countn + 1, var);
                sem_errors++;
            }
            return; 
        }
    }
    
    sprintf(errors[sem_errors], "Line %d: Array argument \"%s\" not found in symbol table!\n", countn + 1, var);
    sem_errors++;
}
