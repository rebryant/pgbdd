#include <stdio.h>
#include <stdlib.h>
#include "graph.h"

/************************ Modifications ***********************
 *
 *  2020-06-08.  Fixed printing problems with unsigned longs.  REB
 *  2020-06-08.  Eliminated unused variable.  REB
 *
 *
 ************************ Modifications ***********************/


Couple::Couple():c1(0),c2(0) {}

Couple::Couple(unsigned long value) {
	this->encode(value);
}

Couple::Couple(unsigned long a1,unsigned long a2):c1(a1),c2(a2) {}

void Couple::decode(unsigned long value,unsigned long m) {
	c1= value/m;
	c2= value%m;
}

unsigned long Couple::encode(unsigned long m) {
	return c1*m+c2;
}

Couple CRules::R1(Couple C) {
	return C;
}

Couple CRules::R2(Couple C,unsigned long m) {
	C.c2=C.c1+C.c2;
	if(C.c2>=m) C.c2%=m;
	return C;
}

Couple CRules::R3(Couple C,unsigned long m) {
	C.c1=C.c1+C.c2;
	if(C.c1>=m) C.c1%=m;
	return C;
}

Couple CRules::R4(Couple C,unsigned long m) {
	C.c2=C.c1+C.c2+1;
	if(C.c2>=m) C.c2%=m;
	return C;
}

Couple CRules::R5(Couple C,unsigned long m) {
	C.c1=C.c1+C.c2+1;
	if(C.c1>=m) C.c1%=m;
	return C;
}

CMatrix::CMatrix():Count(0) {
	for(unsigned int i=0;i<MAXVERTEX;i++)
	{
		Arete[i].NodeNumber=0;
		Arete[i].VertexNumber=0;
	}
}

void CMatrix::Add(unsigned long value) {
	unsigned int Found=0;
	for(unsigned int i=0;i<Count;i++)
	{
		if(Arete[i].NodeNumber==value)
		{
			Found=1;
			return;
		}
	}
	if(!Found)
	{
		Arete[Count].NodeNumber=value;
		Count++;
	}
}

void CMatrix::Replace(unsigned long v1,unsigned long v2) {
	for(unsigned int i=0;i<Count;i++)
		if(Arete[i].NodeNumber==v1)
		{
			Arete[i].NodeNumber=v2;
			return;
		}
}

CGraph::CGraph(unsigned int _m,unsigned int _p):m(_m),p(_p),Nb_Clauses(0),Nb_Var(0) {
	unsigned long matrix_size=m*m*2*MAXVERTEX;
	Matrix=(CMatrix *)new CMatrix[matrix_size];
	if(Matrix==NULL)
	{
		printf("<<< Error Allocating Matrix, M is too big...>>>\n");
		exit(-2);
	}
	else
	{
		printf(" -> Matrix size is %ld Bytes\n",sizeof(Matrix[0]));
		printf(" -> Matrix size is %ld Ko\n",matrix_size*sizeof(Matrix[0])/1024);
	}
}

CGraph::~CGraph() {
	delete Matrix;
}

void CGraph::Generate() {
	Init();
	ApplyRules();
	//PrintMatrix();
	ExpandNodes();
	//PrintMatrix2();
	NumVertex();
}

void CGraph::Init() {
	unsigned long y,x,u,v,z;
	z=m*m;
	for(y=0;y<z;y++)
	{
 		x=(y+1)%z;

		u=y*MAXVERTEX;
		v=x*MAXVERTEX;
		Matrix[u].Add(v);
		Matrix[v].Add(u);

		u=(y+z)*MAXVERTEX;
		v=(x+z)*MAXVERTEX;
		Matrix[u].Add(v);
		Matrix[v].Add(u);
	}
}


void CGraph::PrintMatrix2() {
	unsigned long x,y;
	printf("\n");
	for(y=0;y<m*m*2*MAXVERTEX;y++)
	{
		printf("%3lu) ",y);
		printf("%2d -> ",Matrix[y].Count);
		for(x=0;x<MAXVERTEX;x++)
			printf("%2lu ",Matrix[y].Arete[x].NodeNumber);
		printf("\n");
	}
}


void CGraph::PrintMatrix() {
	unsigned long x,y;
	printf("\n");
	for(y=0;y<m*m*2*MAXVERTEX;y+=MAXVERTEX)
	{
		printf("%3lu) ",y);
		printf("%2d -> ",Matrix[y].Count);
		for(x=0;x<MAXVERTEX;x++)
			printf("%2lu ",Matrix[y].Arete[x].NodeNumber);
		printf("\n");
	}
}

void CGraph::PrintRules() {
	unsigned long x;
	CRules R;
	Couple C,Tmp;
	for(x=0;x<m*m;x++)
	{
		C.decode(x,m);
		Tmp=R.R1(C);	printf(" Rg1->(%ld,%ld)",Tmp.c1,Tmp.c2);
		Tmp=R.R2(C,m);	printf(" Rg2->(%ld,%ld)",Tmp.c1,Tmp.c2);
		Tmp=R.R3(C,m);	printf(" Rg3->(%ld,%ld)",Tmp.c1,Tmp.c2);
		Tmp=R.R4(C,m);	printf(" Rg4->(%ld,%ld)",Tmp.c1,Tmp.c2);
		Tmp=R.R5(C,m);	printf(" Rg5->(%ld,%ld)\n",Tmp.c1,Tmp.c2);
	}
}

void CGraph::ApplyRules() {
	unsigned long y,u,v,m2;
	CRules R;
	Couple C,Tmp;
	m2=m*m;
	for(y=0;y<m2;y++)
	{
			C.decode(y,m);
			u=y*MAXVERTEX;

			v=(R.R1(C  ).encode(m)+m2)*MAXVERTEX;
			Matrix[u].Add(v);
			Matrix[v].Add(u);

			v=(R.R2(C,m).encode(m)+m2)*MAXVERTEX;
			Matrix[u].Add(v);
			Matrix[v].Add(u);

			v=(R.R3(C,m).encode(m)+m2)*MAXVERTEX;
			Matrix[u].Add(v);
			Matrix[v].Add(u);

			v=(R.R4(C,m).encode(m)+m2)*MAXVERTEX;
			Matrix[u].Add(v);
			Matrix[v].Add(u);

			v=(R.R5(C,m).encode(m)+m2)*MAXVERTEX;
			Matrix[u].Add(v);
			Matrix[v].Add(u);
	}
}

void CGraph::ExpandNodes() {
	unsigned long k,x,y,y2,n,C;

 	for(y=0;y<m*m*2*MAXVERTEX;y+=MAXVERTEX)
	{
		C=Matrix[y].Count;

		for(y2=1;y2<C;y2++)
		{
			n=Matrix[y].Arete[y2].NodeNumber;
			Matrix[y].Arete[y2].NodeNumber=0;
			Matrix[y+y2].Add(n);
			Matrix[n].Replace(y,y+y2);
		}

		Matrix[y].Count=1;

		for(k=0;k<C;k++)
		{
			x=(k+1)%C;
			Matrix[k+y].Add(x+y);
			Matrix[x+y].Add(k+y);
		}
	}
}

void CGraph::NumVertex() {
	unsigned long x,y,z,C,C2,n;
	Nb_Var=0;

	for(y=0;y<m*m*2*MAXVERTEX;y++)
		if((C=Matrix[y].Count)!=0)
			for(x=0;x<C;x++)
				if(Matrix[y].Arete[x].VertexNumber==0)
				{
					Nb_Var++;
					//(y,x) = i
					Matrix[y].Arete[x].VertexNumber=Nb_Var;
					//(x,y) = i
					n=Matrix[y].Arete[x].NodeNumber;
					C2=Matrix[n].Count;
					for(z=0;z<C2;z++)
						if(Matrix[n].Arete[z].NodeNumber==y)
						{
							Matrix[n].Arete[z].VertexNumber=Nb_Var;
							z=C2;
						}
				}
}



void CGraph::CountClauses() {
	unsigned long y;
	for(y=0;y<m*m*2*MAXVERTEX;y++)
		if(Matrix[y].Count!=0)	Nb_Clauses++;
}


void CGraph::Output(char *Output_File) {
        unsigned long y;
	long v1,v2,v3;
	unsigned int State=0,ToDo=0;
	unsigned long NbTo1;
	unsigned long NbTo0;
	FILE *f;
	if((f=fopen(Output_File,"wt"))!=NULL)
	{
		CountClauses();

		NbTo1=p*(Nb_Clauses)/100;
		if(NbTo1%2==0) NbTo1++;
		NbTo0=Nb_Clauses-NbTo1;

		printf(" -> %ld variables created\n",Nb_Var);
		printf(" -> %ld * 4 clauses created\n",Nb_Clauses);

		printf(" -> Clauses 0 = %ld\n",NbTo0);
		printf(" -> Clauses 1 = %ld\n",NbTo1);

		fprintf(f,"c\n");
		fprintf(f,"c File made with value :\n");
		fprintf(f,"c	m = %ld\n",m);
		fprintf(f,"c	p = %ld\n",p);
		fprintf(f,"c\n");
		fprintf(f,"c Clauses 0 = %ld\n",NbTo0);
		fprintf(f,"c Clauses 1 = %ld\n",NbTo1);
		fprintf(f,"c\n");
		fprintf(f,"p cnf %ld %ld\n",Nb_Var,Nb_Clauses*4);

		for(y=0;y<m*m*2*MAXVERTEX;y++)
			if(Matrix[y].Count!=0)
			{
				if(State==0)
				{
					State=1;
					ToDo=0;
					if(NbTo0==0) ToDo=1;
				}
				else
				{
					State=0;
					ToDo=1;
					if(NbTo1==0) ToDo=0;

				}
				v1=Matrix[y].Arete[0].VertexNumber;
				v2=Matrix[y].Arete[1].VertexNumber;
				v3=Matrix[y].Arete[2].VertexNumber;
				if(ToDo)
				{
					NbTo1--;
					fprintf(f,"%7ld %7ld %7ld 0\n",-v1,-v2,-v3);
					fprintf(f,"%7ld %7ld %7ld 0\n",-v1, v2, v3);
					fprintf(f,"%7ld %7ld %7ld 0\n", v1,-v2, v3);
					fprintf(f,"%7ld %7ld %7ld 0\n", v1, v2,-v3);
				}
				else
				{
					NbTo0--;
					fprintf(f,"%7ld %7ld %7ld 0\n", v1, v2, v3);
					fprintf(f,"%7ld %7ld %7ld 0\n",-v1,-v2, v3);
					fprintf(f,"%7ld %7ld %7ld 0\n",-v1, v2,-v3);
					fprintf(f,"%7ld %7ld %7ld 0\n", v1,-v2,-v3);
				}
			}
		fclose(f);
	}
	else
		printf("<<< Error while creating file %s...>>>\n",Output_File);
}
