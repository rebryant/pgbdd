#ifndef GRAPH
#define GRAPH

#define MAXVERTEX 7

typedef struct ST_Arete {
	unsigned long 	NodeNumber;
	unsigned long 	VertexNumber;
} ST_Arete;

class CMatrix {
public:
	ST_Arete 		Arete[MAXVERTEX];
	unsigned char 	Count;
	CMatrix();
	void Add(unsigned long value);
	void Replace(unsigned long v1,unsigned long v2);
};

class Couple {
public:
	unsigned long c1,c2;
	Couple();
	Couple(unsigned long value);
	Couple(unsigned long a1,unsigned long a2);
	void decode(unsigned long value,unsigned long m);
	unsigned long encode(unsigned long m);
};

class CRules {
public:
	CRules() {};
	Couple R1(Couple C);
	Couple R2(Couple C,unsigned long m);
	Couple R3(Couple C,unsigned long m);
	Couple R4(Couple C,unsigned long m);
	Couple R5(Couple C,unsigned long m);
};


class CGraph {
private:
	unsigned long m,p;
	unsigned long Nb_Clauses;
	unsigned long Nb_Var;

	CMatrix *Matrix;
public:
	CGraph(unsigned int _m, unsigned int _p);
	~CGraph();

	void PrintMatrix();
	void PrintMatrix2();
	void CountClauses();
	void PrintRules();
	void NumVertex();
	void Generate();
	void Init();
	void ApplyRules();
	void ExpandNodes();
	void Output(char *Output_File);
};


#endif