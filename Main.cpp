#include<iostream>
#include<vector>
#include<string>
#include<sstream>
#include<stack>
#include<stdlib.h>
#include<list>
#include<ctype.h>
#include <stdio.h>
#include<cmath>
#include<set>

using namespace std;

typedef struct AST *pNODE;

struct AST { string info; pNODE children[2]; };

pNODE cons(string, pNODE, pNODE);

string ASTtoString(AST);

list<bool> bits(int, int );
list<string> vars(AST);
list<string> vars(vector<AST> );

bool eval(AST);

list<string> Insert(string, list<string>);
AST substitute(list<bool>, list<string>, AST);
void sub(list<bool>, list<string>, AST);
string validInference(string);
bool symbol(string);
void duplicate(AST *, AST *);

list<string> combine(list<string>, list<string>);

vector<string> combine(vector<string>, vector<string>);

struct tokRslt {
	bool success;
	vector<string> syms;

};

struct parseRslt {
	bool success;
	AST ast;

};

struct inference {
	vector<AST> P;  // premises
	AST ast;    // conclusion
};

struct inferenceRslt {
	bool success;
	inference I;
};

struct premiseRslt {
	bool success;
	vector<AST> V;

};

bool witnessInvalid(list<bool>, list<string>, inference);

bool valid(inference);
premiseRslt Ps(vector<string>, int, int);
inferenceRslt Inf(vector<string>, int, int);
parseRslt B(vector<string>, int, int);
parseRslt I(vector<string>, int, int);
parseRslt D(vector<string>, int, int);
parseRslt C(vector<string>, int, int);
parseRslt N(vector<string>, int, int);
parseRslt U(vector<string>, int, int);
parseRslt Const(vector<string>, int, int);
parseRslt Lvar(vector<string>, int, int);

void prinTree(AST T)
{
	// If both children are NULL, just print the symbol
	if (T.children[0] == NULL) {
		cout << T.info;
		return;
	}

	// print an opening paren, followed by the symbol of T, followed
	// by a space, and then the first child.
	cout << "(" << T.info << " ";
	prinTree(*(T.children[0]));
	cout << " ";

	// print the second child if there is one, and then a right paren.
	if (T.children[1] != NULL)
		prinTree(*(T.children[1]));
	cout << ")";
}


pNODE cons(string s, pNODE c1, pNODE c2)
{
	pNODE ret = new AST;
	ret->info = s; // same as (*ret).info = s
	ret->children[0] = c1;
	ret->children[1] = c2;
	return ret;
}

inferenceRslt parse(vector<string> V) {

	inferenceRslt p;
	int size = V.size();
	p = Inf(V, 0, size);
	return p;
}

string ASTtoString(AST T) //converts an AST to String
{
	string s;
	// If both children are NULL, just print the symbol
	if (T.children[0] == NULL) {
		s = s + T.info;
		return s;
	}

	// print an opening paren, followed by the symbol of T, followed
	// by a space, and then the first child.
	s = s + "(";
	s = s + T.info;
	s = s + " ";
	s += ASTtoString(*(T.children[0]));
	s = s + " ";

	// print the second child if there is one, and then a right paren.
	if (T.children[1] != NULL) {
		s += ASTtoString(*(T.children[1]));
	}
	s = s + ")";
	return s;
}

inferenceRslt Inf(vector<string> L, int i, int j)
{
	// Inf  ::=  Ps ":." Bexp
	inferenceRslt R;
	premiseRslt X;
	parseRslt Y;

	for (int a = i + 1; a < j - 1; a++)
	{
		if (L[a] == ":.")
		{
			X = Ps(L, i, a);
			Y = B(L, a + 1, j);
			if (X.success && Y.success) {
				duplicate(&(Y.ast), &(R.I.ast));
				//R.I.ast = Y.ast;
			for (int i = 0; i < X.V.size(); i++) 
					R.I.P.push_back(X.V[i]);
				
				R.success = true;
				return R;
			}
		}
	}
	R.success = false;
	return R;
}

premiseRslt Ps(vector<string> L, int i, int j) {

	// Ps  ::=  Bexp | Bexp "," Ps
	premiseRslt R,Y;
	parseRslt X;

	X = B(L, i, j);
	if (X.success) {
		R.success = true;
		R.V.push_back(X.ast);
		return R;
	}
	else {
		for (int a = (i + 1); a < j - 1; a++) {
			if (L[a] == ",") {
				X = B(L, i, a);
				Y = Ps(L, a + 1, j);
				if (X.success && Y.success) {
					R.V.push_back(X.ast);
					for (int b = 0; b < Y.V.size(); b++)
						R.V.push_back(Y.V[b]);

					R.success = true;
					return R;
				}
			}
		}
		R.success = false;
		return R;
	}
}

parseRslt B(vector<string> L, int i, int j) {

	parseRslt R, X;

	// B  →   I | I "<=>" B
	X = I(L, i, j);
	if (X.success)
		return X;

	else {
		for (int a = i + 1; a < j - 1; a++) {
			if (L[a] == "<=>") {
				parseRslt Y = I(L, i, a);
				parseRslt Z = B(L, a + 1, j);
				if (Y.success && Z.success) {
					AST * astptr1 = new AST;
					AST * astptr2 = new AST;
					*astptr1 = Y.ast;
					*astptr2 = Z.ast;
					X.ast = *cons("<=>", astptr1, astptr2);
					X.success = true;
					return X;
				}
			}
		}
		X.success = false;
		return X;
	}
}

parseRslt I(vector<string> L, int i, int j) {
	parseRslt R, X;

	// I  →   D | D "=>" I
	X = D(L, i, j);
	if (X.success)
		return X;
	else {
		for (int a = i + 1; a < j - 1; a++) {
			if (L[a] == "=>") {
				//cout << "=> exists in I" << endl;
				parseRslt Y = D(L, i, a);
				parseRslt Z = I(L, (a + 1), j);
				if (Z.success && Y.success) {
					AST * astptr1 = new AST;
					AST * astptr2 = new AST;
					*astptr1 = Y.ast;
					*astptr2 = Z.ast;
					X.ast = *cons("=>", astptr1, astptr2);
					X.success = true;
					return X;
				}
			}
		}
		X.success = false;
		return X;
	}
}

parseRslt D(vector<string> L, int i, int j) {
	parseRslt R, X;
	// D  →   C | D "v" C     
	X = C(L, i, j);
	if (X.success)
		return X;
	else {
		for (int a = (i + 1); a < j - 1; a++) {
			if (L[a] == "v") {

				parseRslt Y = D(L, i, a);
				parseRslt Z = C(L, a + 1, j);
				if (Z.success && Y.success) {
					AST * astptr1 = new AST;
					AST * astptr2 = new AST;
					*astptr1 = Y.ast;
					*astptr2 = Z.ast;
					X.ast = *cons("v", astptr1, astptr2);
					X.success = true;
					return X;
				}
			}
		}
		X.success = false;
		return X;
	}
}

parseRslt C(vector<string> L, int i, int j) {
	parseRslt R, X;
	// C  →   N | C "^" N
	X = N(L, i, j);
	if (X.success)
		return X;
	else {
		for (int a = (i + 1); a < j - 1; a++) {
			if (L[a] == "^") {
				
				parseRslt Y = C(L, i, a);
				parseRslt Z = N(L, a + 1, j);
				if (Z.success && Y.success) {
					AST * astptr1 = new AST;
					AST * astptr2 = new AST;
					*astptr1 = Y.ast;
					*astptr2 = Z.ast;
					X.ast = *cons("^", astptr1, astptr2);
					X.success = true;
					return X;
					
				}
			}
		}
		X.success = false;
		return X;
	}
}

parseRslt N(vector<string> L, int i, int j) {
	parseRslt R, X;
	// test to see if N = U | "~" N

	X = U(L, i, j);
	if (X.success)
		return X;
	else {
		if (L[i] == "~") {
			//cout << "N function success." << endl;
			parseRslt Y = N(L, (i + 1), j);
			if (Y.success) {
				AST * astptr1 = new AST;
				*astptr1 = Y.ast;
				X.ast = *cons("~", astptr1, NULL);
				X.success = true;
				return X;
			}
			else { X.success = false; return X; }
		}
		else
		{
			X.success = false;
			return X;
		}
	}
}

parseRslt U(vector<string> L, int i, int j) {

  //	U :: = Const | "(" B ")" | Lvar
	parseRslt R, X;

	R = Const(L, i, j);
	if (R.success)
		return R;

	R = Lvar(L, i, j);
	if (R.success)
		return R;

	else if (L[i] == "(" && L[j-1] == ")") {
		X = B(L, i + 1, j - 1);
		if (X.success)
			return X;
		else {
			X.success = false;
			return X;
		}
	}
	else {
		X.success = false;
		return X;
	}
}

parseRslt Const(vector<string> L, int i, int j) {

	parseRslt R;

	if ((j - i) == 1 && L[i] == "F") {
		//cout << "Const function: F success" << endl;
		R.success = true;
		R.ast = *cons("F", NULL, NULL);

	}

	else if ((j - i) == 1 && L[i] == "T") {
		//cout << "Const function: T success" << endl;
		R.success = true;
		R.ast = *cons("T", NULL, NULL);
	}
	else {

		R.success = false;
	}
	return R;
}

parseRslt Lvar(vector<string> L, int i, int j) {

	parseRslt P;

	if ((j - i) != 1) { P.success = false; return P; }
	
	if(L[i].size() == 1){

		if (islower(L[i][0]) && L[i][0] != 'v') {
			P.success = true;
			P.ast = *cons(L[i], NULL, NULL);
		}
		else {
			P.success = false;
			return P;
		}
	}
	if (L[i].size() > 1) {
		if (L[i][0] != 'v') {
			for (int a = 0; a < L[i].size(); a++) {
				if (!islower(L[i][a])) { P.success = false; return P; }
			}
			P.success = true;
			P.ast = *cons(L[i], NULL, NULL);
			return P;
		}
		else if(L[i][0] == 'v') {
			P.success = false;
			return P;
		}
	}
	
}

/*parseRslt Lvar(vector<string> L, int i, int j) {

	parseRslt R;
	for (int a = i; a < j; a++) {
		if (L[i] != "v") {
			if (L[a].size() == 1) {
				if (!islower(L[a][0])) {
					 R.success = false;
					 return R; 
				}
			}
			else if (L[a].size() > 1) {
				int s = L[a].size();
				for (int b = 0; b < s; b++) {
					 if (!islower(L[a][b]) && L[a][b] == 'v') { R.success = false; return R; }
				}
			}
		}
		else if (L[i] == "v") { R.success = false; return R; }

	}
	R.success = true;
	string str = "";
	for (int b = i; b < j; b++) {
		if(L[b] != "v"){ str += L[b]; }
	}
		

	R.ast = *cons(str, NULL, NULL);
	return R;
}*/

list<bool> bits(int i, int N) {
	int sum;
	list<bool> B;
	list<bool> B1;
	bool mem;

	if (N > 0 && i >= 0 && i <= (pow(2, N) - 1))
	{
		int quotient;
		int remainder;
		for (int c = 0; c < N; c++) {

			quotient = i / 2;
			remainder = i % 2;

			if (remainder == 0)
				B.push_front(false);
			else 
				B.push_front(true);

			i = quotient;
		}
		return B;
	}
	
	else { return B1; }
}

list<string>  combine(list<string> L1, list<string> L2) {
	list<string> L;

	for (list<string>::iterator it1 = L1.begin(); it1 != L1.end(); it1++) 
		L.push_back(*it1);

	for (list<string>::iterator it2 = L2.begin(); it2 != L2.end(); it2++)
		L.push_back(*it2);

	L.sort();
	L.unique();
	return L;
	
}

list<string> vars(AST T)
{
	list<string> L1;
	parseRslt P;
	vector<string> V;

	if (T.children[0] == NULL) {
		V.push_back(T.info);
		int size = V.size();
		P = Lvar(V, 0, size);
		if (P.success)
			L1.push_back(T.info);
	}
	else if (T.children[0] != NULL && T.children[1] == NULL) {
		return vars(*T.children[0]);
	}
	else if (T.children[0] != NULL && T.children[1] != NULL) {
		return combine(vars(*T.children[0]), vars(*T.children[1]));
	}
	return L1;
}

list<string> vars(vector<AST> Ts) {

	list<string> L;
	int size = Ts.size();

	for (int i = 0; i < size; i++) {
		list<string> L2 = vars(Ts[i]);
		L = combine(L, L2);
	}

	L.sort();
	L.unique();

	return L;
}

list<string> Insert(string s, list<string> *L) {

	bool NotFound = true;

	for (list<string>::iterator it = (*L).begin(); it != (*L).end(); it++)
	{
		if (s == *it)
			NotFound = false;
	}
	if (NotFound) {
		L->push_back(s);
	}
	
	L->sort();

	return (*L);

}
bool eval(AST T) {

	if (T.info == "^") {
		return eval(*T.children[0]) && eval(*T.children[1]);
	}
	else if (T.info == "v")
		return eval(*T.children[0]) || eval(*T.children[1]);
	else if (T.info == "~")
		return !eval(*T.children[0]);
	else if (T.info == "T")
		return true;
	else if (T.info == "F")
		return false;
	else if (T.info == "=>") {
		bool b1, b2;
		b1 = eval(*T.children[0]);
		b2 = eval(*T.children[1]);

		if (b1 && b2)
			return true;
		else if (b1 && !b2)
			return false;
		else if (!b1 && b2)
			return true;
		else if (!b1 && !b2)
			return true;
	}
	else if (T.info == "<=>") {
		bool b1, b2;
		b1 = eval(*T.children[0]);
		b2 = eval(*T.children[1]);

		if (b1 && b2)
			return true;
		else if (b1 && !b2)
			return false;
		else if (!b1 && b2)
			return false;
		else if (!b1 && !b2)
			return true;
	}
}

tokRslt tokenize(string s) {
	
	tokRslt T;
	string t;
	int i,j;
	i = 0;
	int len = s.size();
	T.success = true;

	while (i < len) {

		if (s[i] == ' '){ i = i + 1; }
		else if (s[i] == 'T') {
			T.syms.push_back("T");
			i = i + 1;
		}

		else if (s[i] == 'F') {
			T.syms.push_back("F");
			i = i + 1;
		}
			
		else if (s[i] == 'v') { T.syms.push_back("v"); i = i + 1; }
			
		else if (s[i] == '^') { T.syms.push_back("^"); i = i + 1; }
			
		else if (s[i] == '~') { T.syms.push_back("~"); i = i + 1; }
			
		else if (s[i] == '(') { T.syms.push_back("("); i = i + 1; }
			
		else if (s[i] == ')') { T.syms.push_back(")"); i = i + 1; }
			
		else if (s[i] == ',') { T.syms.push_back(","); i = i + 1; }

		else if (s[i] == ':'&& len > i + 1) {
			i = i + 1;
			if (s[i] == '.') {
				T.syms.push_back(":.");
				i = i + 1;
			}
			else { T.success = false; i = i + 2; }
		}

		else if (s[i] == '='&& len > (i + 1)) {
			i = i + 1;
			if (s[i] == '>') { T.syms.push_back("=>"); i = i + 2; }
				
			else { T.success = false; i = i + 2; }
		}
		else if (s[i] == '<'&& len > i + 2) {
			i = i + 1;
			if (s[i] == '=') {
				i = i + 1;
				if (s[i] == '>') {
					T.syms.push_back("<=>");
					i = i + 1;
				}
				else { T.success = false; i = i + 1; }
					
			}
			else { T.success = false; i = i + 2; }
		}

		else if (islower(s[i]) && s[i] != 'v') {
			j = i;
			while (len > j && islower(s[j]) && s[j] != 'v')
				j += 1;

			t = "";
			for (int a = i; a < j; a++)
				t += s[a];

			T.syms.push_back(t);
			i = i + t.size();
		}
		else { T.success = false; i = i + 1; }
	}
	return T;
}

vector<string>  combine(vector<string> L1, vector<string> L2) {
	vector<string> L;

	for (int i = 0; i < L1.size(); i++)
		L.push_back(L1[i]);

	for (int i = 0; i < L2.size(); i++)
		L.push_back(L2[i]);

	return L;

}

void sub(list<bool> vals, list<string> vars, AST *Exp)
{
	
	int size1 = vals.size();
	int size2 = vars.size();
	vector<bool> V1;
	vector<string> V2;

	for (list<bool>::iterator it = vals.begin(); it != vals.end(); it++)
		V1.push_back(*it);
	
	for (list<string>::iterator id = vars.begin(); id != vars.end(); id++)
		V2.push_back(*id);
	
	if (size1 == size2) {
		if ((*Exp).children[0] == NULL) {
			for (int a = 0; a < size1; a++) {
				if ((*Exp).info == V2[a]) {
					if (V1[a])
						(*Exp).info = "T";
					else
						(*Exp).info = "F";
				}
			}
		}
		else
		{
			sub(vals, vars, (*Exp).children[0]);
		}
		 
		if ((*Exp).children[1] != NULL) {
			 sub(vals, vars, (*Exp).children[1]);
		}
	}
}

void duplicate(AST * A, AST * B) {
	// A is the AST need to be copied

	if (A == NULL){ B = NULL; }
		
	else {
		AST * c1 = new AST;
		AST * c2 = new AST;
		B->info = A->info;
		duplicate(A->children[0], c1);
		duplicate(A->children[1], c2);
		if (c1->info == "") {
			B->children[0] = NULL;
		}else
			B->children[0] = c1;
		if (c2->info == "") {
			B->children[1] = NULL;
		}
		else
			B->children[1] = c2;
	}
}

AST substitute(list<bool> vals, list<string> vars, AST Exp) {
	AST * A = new AST;
	
	duplicate(&Exp,A);
	
	sub(vals, vars, A);

	return *A;
}

bool witnessInvalid(list<bool> vals, list<string> vars, inference I) {

	bool judge, trueOrNot1, trueOrNot2;
	int flag = 0;
	/*cout << "\nBits/Vals: " << endl;
	for (list<bool>::iterator it = vals.begin(); it != vals.end(); it++)
		cout << *it << " ";
	cout << "list<string>: " << endl;
	for (list<string>::iterator id = vars.begin(); id != vars.end(); id++)
		cout << *id << " ";*/

	for (int a = 0; a < I.P.size(); a++) {
		AST T = substitute(vals, vars, I.P[a]);
		
		 trueOrNot1 = eval(T);
		// cout << "trueOrNot1: " << trueOrNot1 << endl;
		 if (trueOrNot1 == false)
		 {
			 flag = 1;  //Break out of loop if any of the premises is False i.e. the Inference is VALID
			 break;
		 }
	}
	
	 AST T = substitute(vals, vars, I.ast);
	trueOrNot2 = eval(T);
	if (flag ==0 && !trueOrNot2)
		return true;
	
	else
		return false;
}

bool valid(inference I) {
	bool judge, trueOrNot1;

	list<string> Vars;

	Vars = vars(I.P);
	list<string> Vars1;
	Vars1 = vars(I.ast);
	
	Vars.merge(Vars1);
	Vars.sort();
	Vars.unique();
		
	int N = Vars.size();
	for (int i = 0; i < pow(2, N); i++) {
		list<bool> vals = bits(i, N);
		if (witnessInvalid(vals, Vars, I)) return false;
	}
	return true;
}

string validInference(string s) {
	tokRslt T;
	list<string> L,L1;
	string result;
	inferenceRslt P;
	bool judge;
	T = tokenize(s);
	
	if (!T.success) return "symbol error";
	
	if (T.syms.size() == 0) return "grammar error";

	P = parse(T.syms);
		
	if (!P.success) return "grammar error";

	if (valid(P.I)) return "valid";
	else if(!valid(P.I))
	{
		return "invalid";
	}
}

int main()
{
	string str = "p ^ ~q => r ^ ~r :. ~p v q";
	string str1 = "q v p :. p v ~q";
	string str2 = "p v q";
	string str3 = " p ^ q";

	tokRslt T = tokenize(str2);
	cout << endl;
	//int size = T.syms.size();

	parseRslt P = Lvar(T.syms, 0, 1);

	if (P.success)
		cout << "P.success: TRUE" << " !" << endl;

	else
		cout << "P.success: False";
	//prinTree(P.ast);

	//inferenceRslt I = parse(T.syms);
	//cout << "\nprint out premise: " << endl;
	//prinTree(I.I.P[0]);
	//cout << "\n second premmise" << endl;
	//prinTree(I.I.P[1]);

	//cout << "\nprint out ast: " << endl;
	//prinTree(I.I.ast);

	//cout << "\n" << validInference(str1) << endl;
	try {
		return 0;
	}
	catch(exception(e)){
		cout << "???" << endl;
	}
}
