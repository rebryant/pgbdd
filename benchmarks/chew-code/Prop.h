#pragma once
#include <iostream>
#include <fstream>
#include <array>
#include <vector>       // std::vector
using namespace std;

struct Clause {
	int lit[4];	// maximum width 4 is all we need
				// use 0 to denote empty slots in clauses

	Clause(int a, int b, int c, int d) {
		lit[0] = a;
		lit[1] = b;
		lit[2] = c;
		lit[3] = d;
	}

	Clause() {
		lit[0] = 0;
		lit[1] = 0;
		lit[2] = 0;
		lit[3] = 0;
	};

	void Display() {
		for (int i = 0; i < 4; i++) {
			cout << lit[i] << " ";
		}
		cout << endl;
	};

	void Print() {
		ofstream cnffile;
		cnffile.open("formula.cnf", ios::app);
		//prooffile << "A";
		for (int i = 0; i < 4; i++) {
			if (lit[i] == 0) {
				break;
			}
			cnffile << lit[i] << " ";
		}
		cnffile << 0 << "\n";
		cnffile.close();
	};

	bool Empty() {
		for (int i = 0; i < 4; i++) {
			if (lit[i] != 0) { return false; }
		}
		return true;
	}
};

struct cnode {
	Clause data;
	cnode *next;
};

class Cnf
{
private:
	//array pointer for first clause
	cnode * head, *tail;
public:
	int cspace;
public:
	Cnf()
	{
		cspace = 0;
		head = NULL;
		tail = NULL;
	}
public:

	bool Empty() { //checks if empty CNF
		return cspace == 0;
	}
	Clause ChooseClause(int pos) {

		{
			cnode *current;
			current = head;
			for (int i = 0; i<pos; i++)
			{
				current = current->next;
			}
			return current->data;
		}
	}
	void AddClause(Clause C) {
		//clauses[cspace] = C;
		cnode *temp = new cnode;
		temp->next = NULL;
		temp->data = C;
		if (head == NULL) {
			head = temp;
			tail = temp;
			temp = NULL;
		}
		else {

			tail->next = temp;
			tail = temp;
		}
		cspace++;
	}

	bool EmpClause() {
		int c = cspace;
		for (int i = 0; i < c; i++)
		{
			Clause C = ChooseClause(i);
			if (C.Empty())
			{
				return 1;
			}

		}
		return 0;
	}

	void Display() {
		//doubprintn('C');
		cnode *temp = new cnode;
		temp = head;
		while (temp != NULL) {
			temp->data.Display();
			//doubprint(0);
			temp = temp->next;
		}


		//std::cin.get();
	}

	void Print() {
		//doubprintn('C');
		cnode *temp = new cnode;
		temp = head;
		while (temp != NULL) {
			temp->data.Print();
			//doubprint(0);
			temp = temp->next;
		}


		//std::cin.get();
	}

	void RmvClauseSimplf(int pos) {
		//for (int j = i; j < cspace; j++) {
		//	clauses[j] = clauses[j + 1];
		//}
		if (pos == 0) {
			head = head->next;
		}
		else {
			cnode *current = new cnode;
			cnode *previous = new cnode;
			current = head;
			for (int i = 0; i<pos; i++)
			{
				previous = current;
				current = current->next;
			}
			previous->next = current->next;
			delete &current;
			delete current;
			delete previous;
		}
		cspace--;
	}

	Clause RmvClauseData(Clause C) {
			cnode *current = new cnode;
			cnode *previous = new cnode;
			current = head;
			int i = 0;
			Clause D;
			bool stop = 0;
			while (current!=nullptr && stop==0)
			{
				if ((C.lit[0] == current->data.lit[0] || C.lit[1] == current->data.lit[0]) || (C.lit[2] == current->data.lit[0] || C.lit[3] == current->data.lit[0])) {
					if ((C.lit[0] == current->data.lit[1] || C.lit[1] == current->data.lit[1]) || (C.lit[2] == current->data.lit[1] || C.lit[3] == current->data.lit[1])) {
						if ((C.lit[0] == current->data.lit[2] || C.lit[1] == current->data.lit[2]) || (C.lit[2] == current->data.lit[2] || C.lit[3] == current->data.lit[2])){
							if ((C.lit[0] == current->data.lit[3] || C.lit[1] == current->data.lit[3]) || (C.lit[2] == current->data.lit[3] || C.lit[3] == current->data.lit[3])){
								if ((C.lit[0] == current->data.lit[0] || C.lit[0] == current->data.lit[1]) || (C.lit[0] == current->data.lit[2] || C.lit[0] == current->data.lit[3])) {
									if ((C.lit[1] == current->data.lit[0] || C.lit[1] == current->data.lit[1]) || (C.lit[1] == current->data.lit[2] || C.lit[1] == current->data.lit[3])) {
										if ((C.lit[2] == current->data.lit[0] || C.lit[2] == current->data.lit[1]) || (C.lit[2] == current->data.lit[2] || C.lit[2] == current->data.lit[3])) {
											if ((C.lit[3] == current->data.lit[0] || C.lit[3] == current->data.lit[1]) || (C.lit[3] == current->data.lit[2] || C.lit[3] == current->data.lit[3])) {

												stop = 1;

											}
										}

									}
								}
							}
						}
					}
				}
				 if (stop==1){
					 if (i == 0) {
						 head = head->next;
						 D = current->data;
						 cspace--;
						 return D;
					 }
					 else {
						 if (i == cspace-1)
						 {
							tail = previous;
							D = current->data;
							previous->next = current->next;
							cspace--;
							return D;
						 }
						 else {
							 previous->next = current->next;
							 D = current->data;
							 //delete &current;
							 //delete current;
							 //delete previous;
							 cspace--;
							 return D;
						 }
					 }
					}
				 else {
					 previous = current;
					 current = current->next;
					 i++;
				 }
			}
			return D;
	}


};

Cnf cnfmerge(Cnf A, Cnf B) {
	Clause C;
	while (B.Empty() == 0) {
		C = B.ChooseClause(0);
		A.AddClause(C);
		B.RmvClauseSimplf(0);
	}
	return A;
}

struct intcnfpair {
	Cnf thecnf;
	int theint;
	intcnfpair(int j, Cnf f) {
		thecnf = f;
		theint = j;
	};
	intcnfpair() {
	};
};

struct boolcnfpair {
	Cnf thecnf;
	bool theint;
	boolcnfpair(int j, Cnf f) {
		thecnf = f;
		theint = j;
	};
	boolcnfpair() {
	};
};

struct swapselcombo {
	int lbound;
	int ubound;
	bool lr;
	int tries;

	swapselcombo(int lb, int ub, bool thebool, int thetries) {
		lbound = lb;
		ubound = ub;
		lr = thebool;
		tries = thetries;
	};
};
