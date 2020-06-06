#include "Prop.h"
#include <fstream>
#include <stack>
#include <math.h>
#include <algorithm>
#include "Tree.h"

#include <ctime>        // std::time
#include <cstdlib>      // std::rand, std::srand

tree reverse(1);
tree second(1);
ofstream myfile;
int display_level = -200;
int proofsize = 0;
int ATAsize = 0;
int RATAsize = 0;
int ATEsize = 0;
int RATEsize = 0;
const int swap_level = 1;
const int xor_level = 5;
const int DRAT_level = -1;
const int tree_levelpswap = 4;
const int tree_leveliswaps = 4;
const int tree_sort = 3;
const int tree_badepth = 3;
const int endexc_level = 2;
int myrandom(int i) { return std::rand() % i; }
int maxextvar = 0;
std::vector<int> extvariables;
bool ERproofonly;


Cnf f;
Cnf Xor(int lit1, int lit2, int lit3){
	Clause C1(-lit1, lit2, lit3, 0);
	Clause C2(lit1, -lit2, lit3, 0);
	Clause C3(lit1, lit2, -lit3, 0);
	Clause C4(-lit1, -lit2, -lit3, 0);
	Cnf X;
	X.AddClause(C1);
	X.AddClause(C2);
	X.AddClause(C3);
	X.AddClause(C4);
	return X;
}

Cnf Parforward(int n, Cnf P) {
	::reverse.source->data = (1);

	int lit1 = 1;
	int lit2 = 2;
	int lit3 = n + 3;

	//this can be copied=================
	::reverse.ExtendSource(n + 3, 2, 1);

	Clause C1(-lit1, lit2, lit3, 0);
	Clause C2(lit1, -lit2, lit3, 0);
	Clause C3(lit1, lit2, -lit3, 0);
	Clause C4(-lit1, -lit2, -lit3, 0);
	P.AddClause(C1);
	P.AddClause(C2);
	P.AddClause(C3);
	P.AddClause(C4);
	if (display_level>= ::endexc_level) {
		cout << "xor" << lit1 << " " << lit2 << " " << lit3 << " ";
	}

	//====This is for forward order================================

	for (int i = 3; i < n + 1; i++) {
		lit1 = i;
		lit2 = n + i ;
		lit3 = n + i + 1;

						  //this can be copied=================
		::reverse.ExtendSource(n + i + 1, i, 1);

		C1 = Clause(-lit1, lit2, lit3, 0);
		C2 = Clause(lit1, -lit2, lit3, 0);
		C3 = Clause(lit1, lit2, -lit3, 0);
		C4 = Clause(-lit1, -lit2, -lit3, 0);
		P.AddClause(C1);
		P.AddClause(C2);
		P.AddClause(C3);
		P.AddClause(C4);
		if (display_level >= ::endexc_level) {
			cout << "xor" << lit1 << " " << lit2 << " " << lit3 << " ";
		}
		//====================================
	}
	lit1 = n + 1;
	lit2 = n + 2;
	lit3 = -(2 * n) - 1; //negate last Tseitin variable
	C1=Clause(-lit1, lit2, lit3, 0);
	C2=Clause(lit1, -lit2, lit3, 0);
	C3=Clause(lit1, lit2, -lit3, 0);
	C4=Clause(-lit1, -lit2, -lit3, 0);
	P.AddClause(C1);
	P.AddClause(C2);
	P.AddClause(C3);
	P.AddClause(C4);
	::reverse.endlit1 = lit1;
	::reverse.endlit2 = lit2;
	if (display_level >= ::endexc_level) {
		cout << "xor" << lit1 << " " << lit2 << " " << lit3 << " ";
	}
	return P;
}


Cnf Parreverse(int n, Cnf P) {
	::reverse.source->data = (n);

	int lit1 = n;
	int lit2 = n - 1;
	int lit3 = n + 1;



	//this can be copied=================
	::reverse.ExtendSource(n + 1, n - 1, 1);

	Clause C1(-lit1, lit2, lit3, 0);
	Clause C2(lit1, -lit2, lit3, 0);
	Clause C3(lit1, lit2, -lit3, 0);
	Clause C4(-lit1, -lit2, -lit3, 0);
	P.AddClause(C1);
	P.AddClause(C2);
	P.AddClause(C3);
	P.AddClause(C4);
	//====This is for reverse order================================

	for (int i = 3; i < n + 1; i++) { //easier to spool if these are added first
		lit1 = n + 1 - i; //Add first parity in reverse order
		lit2 = n + i - 2; //first set of Tseitin variables
		lit3 = n + i - 1; //first set of Tseitin variables

						  //this can be copied=================
		::reverse.ExtendSource(n + i - 1, n + 1 - i, 1);

		C1 = Clause(-lit1, lit2, lit3, 0);
		C2 = Clause(lit1, -lit2, lit3, 0);
		C3 = Clause(lit1, lit2, -lit3, 0);
		C4 = Clause(-lit1, -lit2, -lit3, 0);
		P.AddClause(C1);
		P.AddClause(C2);
		P.AddClause(C3);
		P.AddClause(C4);
		//====================================
	}
	C1 = Clause(-(2 * n - 1), 0, 0, 0);
	P.AddClause(C1);

	return P;
}

Cnf Paroddeven(int n, Cnf P ) {
	::reverse.source->data = (n);

	int lit1 = n;
	int lit2 = n - 2;
	int lit3 = n + 1;



	//this can be copied=================
	::reverse.ExtendSource(n + 1, n - 2, 1);

	Clause C1(-lit1, lit2, lit3, 0);
	Clause C2(lit1, -lit2, lit3, 0);
	Clause C3(lit1, lit2, -lit3, 0);
	Clause C4(-lit1, -lit2, -lit3, 0);
	P.AddClause(C1);
	P.AddClause(C2);
	P.AddClause(C3);
	P.AddClause(C4);
	//====This is for reverse order================================
	int m = floor(n / 2);

	for (int i = 3; i < m + 1; i++) { //easier to spool if these are added first
		lit1 = n + 2 - (2*i); //Add first parity in reverse order
		lit2 = n + i - 2; //first set of Tseitin variables
		lit3 = n + i - 1; //first set of Tseitin variables

						  //this can be copied=================
		::reverse.ExtendSource(n + i - 1, n + 2 - (2 * i), 1);

		C1 = Clause(-lit1, lit2, lit3, 0);
		C2 = Clause(lit1, -lit2, lit3, 0);
		C3 = Clause(lit1, lit2, -lit3, 0);
		C4 = Clause(-lit1, -lit2, -lit3, 0);
		P.AddClause(C1);
		P.AddClause(C2);
		P.AddClause(C3);
		P.AddClause(C4);
		//====================================
	}

	for (int i = 1; i < m + 1; i++) { //easier to spool if these are added first
		lit1 = n + 1 - (2 * i); //Add first parity in reverse order
		lit2 = n + i + m -2; //first set of Tseitin variables
		lit3 = n + i + m -1; //first set of Tseitin variables

						  //this can be copied=================
		::reverse.ExtendSource(n + i + m - 1,n + 1 - (2 * i), 1);

		C1 = Clause(-lit1, lit2, lit3, 0);
		C2 = Clause(lit1, -lit2, lit3, 0);
		C3 = Clause(lit1, lit2, -lit3, 0);
		C4 = Clause(-lit1, -lit2, -lit3, 0);
		P.AddClause(C1);
		P.AddClause(C2);
		P.AddClause(C3);
		P.AddClause(C4);
		//====================================
	}

	if (2*m != n) {
		lit1 = 1; //Add first parity in reverse order
		lit2 = n + m + m - 1; //first set of Tseitin variables
		lit3 = n + m + m ; //first set of Tseitin variables

							  //this can be copied=================
		::reverse.ExtendSource(n + m + m ,1, 1);

		C1 = Clause(-lit1, lit2, lit3, 0);
		C2 = Clause(lit1, -lit2, lit3, 0);
		C3 = Clause(lit1, lit2, -lit3, 0);
		C4 = Clause(-lit1, -lit2, -lit3, 0);
		P.AddClause(C1);
		P.AddClause(C2);
		P.AddClause(C3);
		P.AddClause(C4);
	}

	C1 = Clause(-(2 * n - 1), (3 * n - 2), 0, 0);
	P.AddClause(C1);

	return P;
}
Cnf Parity(int n, std::vector<int> invector, int neglit) {
	//std::vector<int> myvector;
	Cnf P;

	P = Parforward(n, P);

	//===============================
	int lit1 = invector[0];
	int lit2 = invector[1];
	if (neglit == 0) {
		lit1 = -lit1;
	}
	if (neglit == 1) {
		lit2 = -lit2;
	}
	int lit3 = 2 * n+2;
	Clause C1 = Clause(-lit1, lit2, lit3, 0);
	Clause C2 = Clause(lit1, -lit2, lit3, 0);
	Clause C3 = Clause(lit1, lit2, -lit3, 0);
	Clause C4 = Clause(-lit1, -lit2, -lit3, 0);
	P.AddClause(C1);
	P.AddClause(C2);
	P.AddClause(C3);
	P.AddClause(C4);

	for (int i = 3; i < n + 1; i++) {
		lit1 = invector[i-1];
		if (neglit == i-1) {
			lit1 = -lit1;
		}
		lit2 = 2*n-1 + i; //second set of Tseitin variables
		lit3 = 2 * n + i;//second set of Tseitin variables
		C1 = Clause(-lit1, lit2, lit3, 0);
		C2 = Clause(lit1, -lit2, lit3, 0);
		C3 = Clause(lit1, lit2, -lit3, 0);
		C4 = Clause(-lit1, -lit2, -lit3, 0);
		P.AddClause(C1);
		P.AddClause(C2);
		P.AddClause(C3);
		P.AddClause(C4);
	}

	lit1 = invector[n];
	lit2 = invector[n + 1];
	if (neglit == n) {
		lit1 = -lit1;
	}
	if (neglit == n+1) {
		lit2 = -lit2;
	}
	lit3 = -(3 * n) ; //negate last Tseitin variable
	C1 = Clause(-lit1, lit2, lit3, 0);
	C2 = Clause(lit1, -lit2, lit3, 0);
	C3 = Clause(lit1, lit2, -lit3, 0);
	C4 = Clause(-lit1, -lit2, -lit3, 0);
	P.AddClause(C1);
	P.AddClause(C2);
	P.AddClause(C3);
	P.AddClause(C4);

	return P;
}

void ATA(Clause C) {
	if (::display_level > ::DRAT_level) {
		std::cout << "ATA ";
		C.Display();
	}
	::proofsize++;
	::ATAsize++;
	//ofstream prooffile;
	//prooffile.open("proof.txt", ios::app);
	//prooffile << "A";
	//for (int i = 0; i < 4; i++) {
	//	if (C.lit[i] == 0) {
	//		break;
	//	}
	//		prooffile << C.lit[i] << " ";
	//}
	//prooffile << 0 << "\n";
	//prooffile.close();

	//p.AddClause(C);
	return;


}

void RATA(Clause C, int l) {
	if (::display_level > ::DRAT_level) {
		std::cout << l << " RATA ";
		C.Display();
	}
	::proofsize++;
	::RATAsize++;
	//ofstream prooffile;
	//prooffile.open("proof.txt", ios::app);
	//prooffile << "A";

	//prooffile.close();

	//p.AddClause(C);
	return;
}


void ATE(Clause C) {
	if (::display_level > ::DRAT_level) {
		std::cout << "ATE ";
		//Clause D = p.RmvClauseData(C);
		C.Display();
	}
	::proofsize++;
	::ATEsize++;
	//ofstream prooffile;
	//prooffile.open("proof.txt", ios::app);
	//prooffile << "d ";
	//for (int i = 0; i < 4; i++) {
	//	if (C.lit[i] == 0) {
	//		break;
	//	}
	//	prooffile << C.lit[i] << " ";
	//}
	//prooffile << 0 << "\n";
	//prooffile.close();

	return;
}

void RATE(Clause C, int l) {
	if (::display_level > ::DRAT_level) {
		std::cout << l << " RATE ";
		//Clause D = p.RmvClauseData(C);
		C.Display();
	}
	::proofsize++;
	::RATEsize++;
	//ofstream prooffile;
	//prooffile.open("proof.txt", ios::app);

	//prooffile.close();

	return;
}


void Clauseshift(int lit1, int lit2, int lit3, int lit4, int elim) {
	ofstream prooffile;
	prooffile.open("formula.drat", ios::app);

	if (::ERproofonly) {
		::maxextvar++;
		::extvariables[abs(elim) - 1] = maxextvar;

		if (lit1>0) {
			lit1 = ::extvariables[abs(lit1) - 1];
		}
		else {
			lit1 = -::extvariables[abs(lit1) - 1];
		}

		if (lit2 > 0) {
			lit2 = ::extvariables[abs(lit2) - 1];
		}
		else {
			lit2 = -::extvariables[abs(lit2) - 1];
		}

		if (lit3 > 0) {
			lit3 = ::extvariables[abs(lit3) - 1];
		}
		else {
			lit3 = -::extvariables[abs(lit3) - 1];
		}

		if (lit4 > 0) {
			lit4 = ::extvariables[abs(lit4) - 1];
		}
		else {
			lit4 = -::extvariables[abs(lit4) - 1];
		}

		if (elim) {
			elim = ::extvariables[abs(elim) - 1];
		}
		else{
			elim = -::extvariables[abs(elim) - 1];
		}



	}

	Clause tern1(-lit1, lit2, lit3, lit4);
	Clause tern2(lit1, -lit2, lit3, lit4);
	Clause tern3(lit1, lit2, -lit3, lit4);
	Clause tern4(lit1, lit2, lit3, -lit4);
	Clause tern5(-lit1, -lit2, -lit3, lit4);
	Clause tern6(lit1, -lit2, -lit3, -lit4);
	Clause tern7(-lit1, lit2, -lit3, -lit4);
	Clause tern8(-lit1, -lit2, lit3, -lit4);

	if (::display_level > ::xor_level) {
		cout << "adding terns" << endl;
	}
	ATA(tern1);
	for (int i = 0; i < 4; i++) {
		if (tern1.lit[i] == 0) {
			break;
		}
		prooffile << tern1.lit[i] << " ";
	}
	prooffile << 0 << "\n";

	ATA(tern2);
	for (int i = 0; i < 4; i++) {
		if (tern2.lit[i] == 0) {
			break;
		}
		prooffile << tern2.lit[i] << " ";
	}

	prooffile << 0 << "\n";
	ATA(tern3);
	for (int i = 0; i < 4; i++) {
		if (tern3.lit[i] == 0) {
			break;
		}
		prooffile << tern3.lit[i] << " ";
	}

	prooffile << 0 << "\n";


	ATA(tern4);
	for (int i = 0; i < 4; i++) {
		if (tern4.lit[i] == 0) {
			break;
		}
		prooffile << tern4.lit[i] << " ";
	}

	prooffile << 0 << "\n";

	ATA(tern5);
	for (int i = 0; i < 4; i++) {
		if (tern5.lit[i] == 0) {
			break;
		}
		prooffile << tern5.lit[i] << " ";
	}

	prooffile << 0 << "\n";

	ATA(tern6);
	for (int i = 0; i < 4; i++) {
		if (tern6.lit[i] == 0) {
			break;
		}
		prooffile << tern6.lit[i] << " ";
	}

	prooffile << 0 << "\n";


	ATA(tern7);
	for (int i = 0; i < 4; i++) {
		if (tern7.lit[i] == 0) {
			break;
		}
		prooffile << tern7.lit[i] << " ";
	}

	prooffile << 0 << "\n";

	ATA(tern8);
	for (int i = 0; i < 4; i++) {
		if (tern8.lit[i] == 0) {
			break;
		}
		prooffile << tern8.lit[i] << " ";
	}

	prooffile << 0 << "\n";

	if (::ERproofonly) {
		Clause axor1(-elim, lit3, lit4, 0);
		Clause axor2(elim, -lit3, lit4, 0);
		Clause axor3(elim, lit3, -lit4, 0);
		Clause axor4(-elim, -lit3, -lit4, 0);
		Clause axor5(-elim, lit1, lit2, 0);
		Clause axor6(elim, -lit1, lit2, 0);
		Clause axor7(elim, lit1, -lit2, 0);
		Clause axor8(-elim, -lit1, -lit2, 0);



		if (::display_level > ::xor_level) {
			cout << "adding lower xors" << endl;
		}
		RATA(axor1, -elim);
		for (int i = 0; i < 4; i++) {
			if (axor1.lit[i] == 0) {
				break;
			}
			prooffile << axor1.lit[i] << " ";
		}
		prooffile << 0 << "\n";

		RATA(axor2, -elim);
		for (int i = 0; i < 4; i++) {
			if (axor2.lit[i] == 0) {
				break;
			}
			prooffile << axor2.lit[i] << " ";
		}
		prooffile << 0 << "\n";
		RATA(axor3, -elim);
		for (int i = 0; i < 4; i++) {
			if (axor3.lit[i] == 0) {
				break;
			}
			prooffile << axor3.lit[i] << " ";
		}
		prooffile << 0 << "\n";

		RATA(axor4, -elim);
		for (int i = 0; i < 4; i++) {
			if (axor4.lit[i] == 0) {
				break;
			}
			prooffile << axor4.lit[i] << " ";
		}
		prooffile << 0 << "\n";

		Clause imed1(-lit1, -lit2, -elim, lit4);
		Clause imed2(-lit1, -lit2, -elim, -lit4);
		Clause imed3(-lit1, lit2, elim, lit4);
		Clause imed4(-lit1, lit2, elim, -lit4);
		Clause imed5(lit1, -lit2, elim, lit4);
		Clause imed6(lit1, -lit2, elim, -lit4);
		Clause imed7(lit1, lit2, -elim, lit4);
		Clause imed8(lit1, lit2, -elim, -lit4);

		///Resolve on lit3
		ATA(imed1);
		for (int i = 0; i < 4; i++) {
			if (imed1.lit[i] == 0) {
				break;
			}
			prooffile << imed1.lit[i] << " ";
		}
		prooffile << 0 << "\n";

		ATA(imed2);
		for (int i = 0; i < 4; i++) {
			if (imed2.lit[i] == 0) {
				break;
			}
			prooffile << imed2.lit[i] << " ";
		}
		prooffile << 0 << "\n";

		ATA(imed3);
		for (int i = 0; i < 4; i++) {
			if (imed3.lit[i] == 0) {
				break;
			}
			prooffile << imed3.lit[i] << " ";
		}
		prooffile << 0 << "\n";

		ATA(imed4);
		for (int i = 0; i < 4; i++) {
			if (imed4.lit[i] == 0) {
				break;
			}
			prooffile << imed4.lit[i] << " ";
		}
		prooffile << 0 << "\n";

		ATA(imed5);
		for (int i = 0; i < 4; i++) {
			if (imed5.lit[i] == 0) {
				break;
			}
			prooffile << imed5.lit[i] << " ";
		}
		prooffile << 0 << "\n";

		ATA(imed6);
		for (int i = 0; i < 4; i++) {
			if (imed6.lit[i] == 0) {
				break;
			}
			prooffile << imed6.lit[i] << " ";
		}
		prooffile << 0 << "\n";

		ATA(imed7);
		for (int i = 0; i < 4; i++) {
			if (imed7.lit[i] == 0) {
				break;
			}
			prooffile << imed7.lit[i] << " ";
		}
		prooffile << 0 << "\n";

		ATA(imed8);
		for (int i = 0; i < 4; i++) {
			if (imed8.lit[i] == 0) {
				break;
			}
			prooffile << imed8.lit[i] << " ";
		}
		prooffile << 0 << "\n";

		//resolve on lit4


		if (::display_level > ::xor_level) {
			cout << "adding upper xors" << endl;
		}
		ATA(axor5);
		for (int i = 0; i < 4; i++) {
			if (axor5.lit[i] == 0) {
				break;
			}
			prooffile << axor5.lit[i] << " ";
		}

		prooffile << 0 << "\n";


		ATA(axor6);
		for (int i = 0; i < 4; i++) {
			if (axor6.lit[i] == 0) {
				break;
			}
			prooffile << axor6.lit[i] << " ";
		}

		prooffile << 0 << "\n";



		ATA(axor7);
		for (int i = 0; i < 4; i++) {
			if (axor7.lit[i] == 0) {
				break;
			}
			prooffile << axor7.lit[i] << " ";
		}

		prooffile << 0 << "\n";



		ATA(axor8);
		for (int i = 0; i < 4; i++) {
			if (axor8.lit[i] == 0) {
				break;
			}
			prooffile << axor8.lit[i] << " ";
		}

		prooffile << 0 << "\n";

	}
	else {


		Clause dxor1(-elim, lit2, lit3, 0);
		Clause dxor2(elim, -lit2, lit3, 0);
		Clause dxor3(elim, lit2, -lit3, 0);
		Clause dxor4(-elim, -lit2, -lit3, 0);
		Clause dxor5(-elim, lit1, lit4, 0);
		Clause dxor6(elim, -lit1, lit4, 0);
		Clause dxor7(elim, lit1, -lit4, 0);
		Clause dxor8(-elim, -lit1, -lit4, 0);

		if (::display_level > ::xor_level) {
			cout << "eliminating upper xors" << endl;
		}

		RATE(dxor2, elim);
		prooffile << "d ";
		for (int i = 0; i < 4; i++) {
			if (dxor2.lit[i] == 0) {
				break;
			}
			prooffile << dxor2.lit[i] << " ";
		}
		prooffile << 0 << "\n";

		RATE(dxor3, elim);
		prooffile << "d ";
		for (int i = 0; i < 4; i++) {
			if (dxor3.lit[i] == 0) {
				break;
			}
			prooffile << dxor3.lit[i] << " ";
		}
		prooffile << 0 << "\n";

		RATE(dxor6, elim);
		prooffile << "d ";
		for (int i = 0; i < 4; i++) {
			if (dxor6.lit[i] == 0) {
				break;
			}
			prooffile << dxor6.lit[i] << " ";
		}
		prooffile << 0 << "\n";


		RATE(dxor7, elim);
		prooffile << "d ";
		for (int i = 0; i < 4; i++) {
			if (dxor7.lit[i] == 0) {
				break;
			}
			prooffile << dxor7.lit[i] << " ";
		}
		prooffile << 0 << "\n";


		if (::display_level > ::xor_level) {
			cout << "eliminating lower xors" << endl;
		}
		RATE(dxor1, -elim);
		prooffile << "d ";
		for (int i = 0; i < 4; i++) {
			if (dxor1.lit[i] == 0) {
				break;
			}
			prooffile << dxor1.lit[i] << " ";
		}
		prooffile << 0 << "\n";


		RATE(dxor4, -elim);
		prooffile << "d ";
		for (int i = 0; i < 4; i++) {
			if (dxor4.lit[i] == 0) {
				break;
			}
			prooffile << dxor4.lit[i] << " ";
		}
		prooffile << 0 << "\n";

		RATE(dxor5, -elim);
		prooffile << "d ";
		for (int i = 0; i < 4; i++) {
			if (dxor5.lit[i] == 0) {
				break;
			}
			prooffile << dxor5.lit[i] << " ";
		}
		prooffile << 0 << "\n";

		RATE(dxor8, -elim);
		prooffile << "d ";
		for (int i = 0; i < 4; i++) {
			if (dxor8.lit[i] == 0) {
				break;
			}
			prooffile << dxor8.lit[i] << " ";
		}
		prooffile << 0 << "\n";

		Clause axor1(-elim, lit3, lit4, 0);
		Clause axor2(elim, -lit3, lit4, 0);
		Clause axor3(elim, lit3, -lit4, 0);
		Clause axor4(-elim, -lit3, -lit4, 0);
		Clause axor5(-elim, lit1, lit2, 0);
		Clause axor6(elim, -lit1, lit2, 0);
		Clause axor7(elim, lit1, -lit2, 0);
		Clause axor8(-elim, -lit1, -lit2, 0);

		if (::display_level > ::xor_level) {
			cout << "adding lower xors" << endl;
		}
		RATA(axor1, -elim);
		for (int i = 0; i < 4; i++) {
			if (axor1.lit[i] == 0) {
				break;
			}
			prooffile << axor1.lit[i] << " ";
		}
		prooffile << 0 << "\n";

		RATA(axor4, -elim);
		for (int i = 0; i < 4; i++) {
			if (axor4.lit[i] == 0) {
				break;
			}
			prooffile << axor4.lit[i] << " ";
		}
		prooffile << 0 << "\n";
		RATA(axor5, -elim);
		for (int i = 0; i < 4; i++) {
			if (axor5.lit[i] == 0) {
				break;
			}
			prooffile << axor5.lit[i] << " ";
		}
		prooffile << 0 << "\n";

		RATA(axor8, -elim);
		for (int i = 0; i < 4; i++) {
			if (axor8.lit[i] == 0) {
				break;
			}
			prooffile << axor8.lit[i] << " ";
		}
		prooffile << 0 << "\n";


		if (::display_level > ::xor_level) {
			cout << "adding upper xors" << endl;
		}
		RATA(axor2, elim);
		for (int i = 0; i < 4; i++) {
			if (axor5.lit[i] == 0) {
				break;
			}
			prooffile << axor2.lit[i] << " ";
		}

		prooffile << 0 << "\n";


		RATA(axor3, elim);
		for (int i = 0; i < 4; i++) {
			if (axor6.lit[i] == 0) {
				break;
			}
			prooffile << axor3.lit[i] << " ";
		}

		prooffile << 0 << "\n";



		RATA(axor6, elim);
		for (int i = 0; i < 4; i++) {
			if (axor6.lit[i] == 0) {
				break;
			}
			prooffile << axor6.lit[i] << " ";
		}

		prooffile << 0 << "\n";



		RATA(axor7, elim);
		for (int i = 0; i < 4; i++) {
			if (axor7.lit[i] == 0) {
				break;
			}
			prooffile << axor7.lit[i] << " ";
		}

		prooffile << 0 << "\n";



		if (::display_level > ::xor_level) {
			cout << "eliminating terns" << endl;
		}
		ATE(tern1);
		prooffile << "d ";
		for (int i = 0; i < 4; i++) {
			if (tern1.lit[i] == 0) {
				break;
			}
			prooffile << tern1.lit[i] << " ";
		}
		prooffile << 0 << "\n";


		ATE(tern2);
		prooffile << "d ";
		for (int i = 0; i < 4; i++) {
			if (tern2.lit[i] == 0) {
				break;
			}
			prooffile << tern2.lit[i] << " ";
		}
		prooffile << 0 << "\n";


		ATE(tern3);
		prooffile << "d ";
		for (int i = 0; i < 4; i++) {
			if (tern3.lit[i] == 0) {
				break;
			}
			prooffile << tern3.lit[i] << " ";
		}
		prooffile << 0 << "\n";

		ATE(tern4);
		prooffile << "d ";
		for (int i = 0; i < 4; i++) {
			if (tern4.lit[i] == 0) {
				break;
			}
			prooffile << tern4.lit[i] << " ";
		}
		prooffile << 0 << "\n";

		ATE(tern5);
		prooffile << "d ";
		for (int i = 0; i < 4; i++) {
			if (tern5.lit[i] == 0) {
				break;
			}
			prooffile << tern5.lit[i] << " ";
		}
		prooffile << 0 << "\n";


		ATE(tern6);
		prooffile << "d ";
		for (int i = 0; i < 4; i++) {
			if (tern6.lit[i] == 0) {
				break;
			}
			prooffile << tern6.lit[i] << " ";
		}
		prooffile << 0 << "\n";


		ATE(tern7);
		prooffile << "d ";
		for (int i = 0; i < 4; i++) {
			if (tern7.lit[i] == 0) {
				break;
			}
			prooffile << tern7.lit[i] << " ";
		}
		prooffile << 0 << "\n";


		ATE(tern8);
		prooffile << "d ";
		for (int i = 0; i < 4; i++) {
			if (tern8.lit[i] == 0) {
				break;
			}
			prooffile << tern8.lit[i] << " ";
		}
		prooffile << 0 << "\n";

	}
	prooffile.close();
	return;
	}

bool swapend(tnode* swap1, bool dir) {
	bool dir1 = swap1->lr;
	tnode* par1 = swap1->parent;
	tnode* otherchild;
	if (dir1 == 0) {
		otherchild = par1->child2;
	}
	else {
		otherchild = par1->child1;
	}
	int litswap1 = swap1->data;
	int litswap2 = ::reverse.endlit1;
	int litpar1 = par1->data;
	int litpar2 = -::reverse.endlit2;
	int litnoswap = otherchild->data;
	if (dir == 1) {
		litswap2 = ::reverse.endlit2;
		litpar2 = -::reverse.endlit1;
	}
	Clauseshift(litpar2, litswap1, litnoswap, litswap2, litpar1);
	if (dir == 1) {
		::reverse.endlit2=litswap1;
	}
	else {
		::reverse.endlit1 = litswap1;
	}
	if (display_level > ::endexc_level) {
		::reverse.print();
	}
	if (dir1 == 0) {
		par1->child1 = par1->child3;
		par1->child1->lr = 0;
	}
	else {
		par1->child2 = par1->child3;
		par1->child2->lr = 1;
	}
	par1->child3 = swap1;

	return dir1;
}

void swapdown(tnode* swap1, bool dir) {
	//dir gives direction of otherchild's child that we keep
	tnode* par1 = swap1->parent;
	tnode* otherchild;
	bool dir1 = swap1->lr;
	if (dir1 == 0) {
		otherchild = par1->child2;
	}
	else {
		otherchild = par1->child1;
	}
	tnode* swap2;
	int litnoswap;
	if (dir == 0) {
		swap2 = otherchild->child2;
		otherchild->child2 = swap1;
		otherchild->child2->parent = otherchild;
		otherchild->child2->lr = 1;
		litnoswap = otherchild->child1->data;
	}
	else {
		swap2 = otherchild->child1;
		otherchild->child1 = swap1;
		otherchild->child1->parent = otherchild;
		otherchild->child1->lr = 0;
		litnoswap = otherchild->child2->data;
	}
	if (dir1 == 0) {
		par1->child1 = swap2;
		par1->child1->parent = par1;
		par1->child1->lr = 0;
	}
	else {
		par1->child2 = swap2;
		par1->child2->parent = par1;
		par1->child2->lr = 1;
	}
	int litswap1 = swap1->data;
	int litswap2 = swap2->data;
	int litpar1 = par1->data;
	int litpar2 = otherchild->data;


	//Put Cnf stuff here
	Clauseshift(litpar1, litswap2, litnoswap, litswap1, litpar2);

	if (::display_level > ::tree_leveliswaps) {
		::reverse.print();
	}
	return;
}
bool swapup(tnode* swap1, Cnf f) {
	int litswap1 = swap1->data;
	tnode* par1 = swap1->parent;

	if (par1 == NULL) {
		cout << "error no parent" << endl;
	}
	int litpar1 = par1->data;
	bool dir1 = swap1->lr;
	tnode* par2 = par1->parent;
	if (par2 == NULL) {
		return 0;
	}
	int litpar2 = par2->data;
	bool dir2 = par1->lr;
	tnode* swap2;
	int litswap2;
	int retval=1+dir1+2*dir2;
	//this is where swapping occurs
	if (dir2 == 0) {
		swap2 = par2->child2;
		litswap2 = swap2->data;
		par2->child2 = swap1;
		par2->child2->lr = 1;
		swap1->parent = par2;
	}
	else {
		swap2 = par2->child1;
		litswap2 = swap2->data;
		par2->child1 = swap1;
		par2->child1->lr = 0;
		swap1->parent = par2;
	}
	int litnoswap;
	if (dir1 == 0) {
		par1->child1 = swap2;
		litnoswap = par1->child2->data;
		par1->child1->lr = 0;
		swap2->parent = par1;
	}
	else {
		par1->child2 = swap2;
		litnoswap = par1->child1->data;
		par1->child2->lr = 1;
		swap2->parent = par1;
	}

	Clauseshift(litpar2, litswap1, litnoswap, litswap2, litpar1);
	//REMOVED no swap -now swap children of par2 to make things easier
	//tnode* temp = par2->child1;
	//par2->child1 = par2->child2;
	//par2->child1->lr = 0;
	//par2->child2 = temp;
	//par2->child2->lr = 1;
	if (::display_level > ::tree_leveliswaps) {
		::reverse.print();
	}

	return dir1;
}

tree rebalance(tree g, bool r) {//a0 is Tseitin variable
	if (g.depth <= 2) {
		return g; // already log depth
	}
	float noofinternals = (g.depth - 2);
	float halfinternals = (noofinternals / 2);
	if (!r) {
		// we will add ceil n / 2 Tseitin variables to g2
		for (int i = 0; i < ceil(halfinternals); i++) {
			int lit1 = g.source->data;
			int lit2 = g.source->child1->child1->data;
			int lit3 = g.source->child1->child2->data;
			int lit4 = g.source->child2->data;
			int elim = g.source->child1->data;

			::Clauseshift(lit1, lit2, lit3, lit4, elim);

			g.treeshiftr();
		}

	}
	else {
		for (int i = 0; i < floor(halfinternals); i++) {

			int lit1 = g.source->data;
			int lit2 = g.source->child2->child2->data;
			int lit3 = g.source->child2->child1->data;
			int lit4 = g.source->child1->data;
			int elim = g.source->child2->data;

			::Clauseshift(lit1, lit2, lit3, lit4, elim);

			g.treeshiftl();

		}
	}

	tree g1(g.source->child1); //the left tree
	tree g2(g.source->child2); //the right tree
	g1.depth = floor(halfinternals) +1;
	g2.depth = ceil(halfinternals) +1;
	g.depth = max(g1.depth, g2.depth) + 1;
	g1=rebalance(g1, 0);
	g2=rebalance(g2, 1);
	g.depth = max(g1.depth, g2.depth) + 1;
	//merge the two cnfs and return
	return g;
}

tnode* sleaf(int i, int n, tnode* t) {
	if (n == 1) {
		return t;
	}

	float m = n / 2;
	int j = i;
	if (j <= floor(m)) {
		return sleaf(j, floor(m), t->child1);
	}
	else
	{
		return sleaf(j-floor(m), n-floor(m), t->child2);
	}

}

Cnftnodepair spushdown(int i, int n, tnode* pivot, tnode* swapitem, Cnf f) {
	Cnftnodepair joint;
	joint.form = f; //preparing formula
	if (n == 1) {
		joint.nodestar = pivot;
		return joint;
	}

	float m = n / 2;
	int j = i;
	if (j <= floor(m)) {
		//swapdown(swapitem, f);
		return spushdown(j, floor(m), pivot->child1, swapitem, f);
	}
	else
	{
		return spushdown(j - floor(m), n - floor(m), pivot->child2, swapitem, f);
	}

}

void swapping(int n, Cnf f, std::vector<int> invector) {
	bool inpos = 0;
	while (inpos == 0) {
		inpos = 1; //this will become false if any leaf is in the wrong position
		tnode* selection = ::reverse.source;
		int rangedown = 1; //the currently selected node has a range of positions
		int rangeup = n;
		stack<swapselcombo> selectpos; //swapselcombo
		selectpos.push(swapselcombo(rangedown, rangeup+2, 0, 0));
		if (display_level >= endexc_level) {
			cout << "pushing excp" << rangedown << " " << rangeup + 2 << endl;
		}
		selectpos.push(swapselcombo(rangedown, rangeup, 0, 0));
		bool isselectionaleaf = 0;
		bool endexcept = 0;
		while (!selectpos.empty()) { //this traverses all nodes
			isselectionaleaf = 1;

			//recalculate the ranges
			rangedown = selectpos.top().lbound;
			rangeup = selectpos.top().ubound;
			float rangemid = (rangedown + rangeup);
			rangemid = rangemid / 2;
			int tries = selectpos.top().tries;
			if (endexcept) {

			}
			if (selectpos.top().tries == 0) {
				if (selection->child1 != NULL) {
					isselectionaleaf = 0;
					selectpos.top().tries++;

					if (endexcept) {}
					else {
						if (::display_level > ::swap_level) {
							cout << "moving left" << endl;
						}
						selection = selection->child1;
						rangeup = ceil(rangemid) - 1;
						selectpos.push(swapselcombo(rangedown, rangeup, 0, 0));
					}
				}
			}
			else {
				if (selectpos.top().tries == 1) {
					if (selection->child2 != NULL) {
						isselectionaleaf = 0;
						selectpos.top().tries++;

						if (endexcept) {}
						else {
							if (::display_level > ::swap_level) {
								cout << "moving right" << endl;
							}
							selection = selection->child2;
							rangedown = ceil(rangemid);
							selectpos.push(swapselcombo(rangedown, rangeup, 0, 0));
						}
					}
				}
				else {
					if (selectpos.top().tries > 1) {
						isselectionaleaf = 0;
						if (::display_level > ::swap_level) {
							cout << "moving up" << endl;
						}
						if (selection->parent != NULL) {
							selection = selection->parent;
						}
						else {
							endexcept = 1;
						}
						isselectionaleaf = 0;
						selectpos.pop();
					}
				}
			}
			bool enddir = 0;
			if(endexcept && (!selectpos.empty())) { //new code to deal with endlits
				int endvalue;

				if (selectpos.top().tries == 0) {
					endvalue = ::reverse.endlit1;
				}
				else {
					endvalue = ::reverse.endlit2;
					enddir = 1;
				}

				if (::display_level > ::endexc_level) {
					cout << "found endleaf with data " << endvalue;
				}
				int enddata = endvalue;

				endvalue = abs(invector[endvalue - 1]);
				if (::display_level > ::endexc_level) {
					cout <<"and value " << endvalue << endl;
				}
				if (endvalue > n){
					if ((selectpos.top().tries == 0)&&(endvalue==n+2)) {
						::reverse.endlit1 = ::reverse.endlit2;
						::reverse.endlit2=enddata;
					}
					else {
						if ((selectpos.top().tries == 1) && (endvalue == n + 1)) {
							::reverse.endlit2= ::reverse.endlit1;
							::reverse.endlit1 = enddata;
						}
					}
				}
				else {
					rangeup = n;
					rangedown = 1;
					//put literal in child 3 position
					//perform clauseshift
					//now next swapdown puts it in realtree and subtree in child3 position
					//however remember to swap out the poor subtree in child3 position on the way back up
					//end by
					selection = new tnode(enddata);
					::reverse.source->child3 = selection;
					selection->parent = ::reverse.source;
					rangemid = rangeup + rangedown;
					rangemid = rangemid / 2;
					tnode* temp;
					if (ceil(rangemid) <= endvalue) {
						swapend(::reverse.source->child1,enddir);
						rangedown = ceil(rangemid);
					}
					else {
						swapend(::reverse.source->child2, enddir);
						rangeup = ceil(rangemid)-1;
					}
					//sameendstuff as later
					isselectionaleaf = 1;
				}
			}


			if (isselectionaleaf) {
				int value = selection->data;
				value = abs(invector[value - 1]);
				int firstlevelexception = 2;
				stack<bool> reverseswaps;
				bool inleafposition = 1;
				tnode* selection2 = selection;
				//getchar();

				if (::display_level > ::swap_level) {
					cout << "found leaf with data " << selection->data << "and value " << value << endl;
				}
				if (value != selectpos.top().lbound || value != selectpos.top().ubound) {
					if (!endexcept) {
						rangeup = selectpos.top().ubound;
						rangedown = selectpos.top().lbound;
						inpos = false;
						//now we have found a leaf to swap
						// here we can use value to find the swapping position
						stack<swapselcombo> selectposcopy = selectpos;

						if (selection->lr == 0) {
							firstlevelexception = 0;
						}
						else {
							firstlevelexception = 1;
						}

						if (::display_level > ::swap_level) {
							cout << selection->data << "not in range " << rangedown << "to" << rangeup << endl;
						}
						bool notinrange = 1;
						inleafposition = 1;
						selection2 = selection;
						while (notinrange) { //the loop for the first push up
							selectposcopy.pop();// this means bounds will be for parent of selection

							if (selectposcopy.top().lbound <= value && selectposcopy.top().ubound >= value) {
								notinrange = 0;
								if (::display_level > ::swap_level) {
									cout << selection->data << "is in the right range " << selectposcopy.top().lbound << "to" << selectposcopy.top().ubound << endl;
								}
								//::reverse.print();
								if (value > n) {
									bool b;
									if (value == n + 1) {
										tnode* thirdnde = new tnode(::reverse.endlit1);
										::reverse.source->child3 = thirdnde;
										thirdnde->parent = ::reverse.source;
										b = swapend(selection, 0);

									}
									else {
										tnode* thirdnde = new tnode(::reverse.endlit2);
										::reverse.source->child3 = thirdnde;
										thirdnde->parent = ::reverse.source;
										b = swapend(selection, 1);

									}
									if (!b) {
										selection = selection->parent->child1;
									}
									else {
										selection = selection->parent->child2;
									}
								}

							}
							else {

								if (::display_level > ::swap_level) {
									cout << selection->data << "not in range " << selectposcopy.top().lbound << "to" << selectposcopy.top().ubound << endl;
								}
								if (selection->lr == 0) {
									firstlevelexception = 0;
								}
								else {
									firstlevelexception = 1;
								}
								bool g;
								if (selection->parent->parent != NULL) {
									g = swapup(selection, f);
									reverseswaps.push(g);
								}


								inleafposition = 0;

								selection2 = selection->parent;

								//::reverse.print();

							}
						}
						rangeup = selectposcopy.top().ubound;
						rangedown = selectposcopy.top().lbound;

					}
					else
					{
						inleafposition = 0;
					}
					//now swapdown 
					int downlevels = 0;
					bool downswapdir = 0;
					bool stopswapdown = 0;



					tnode* sibling = selection;
					tnode* selectionswap = selection;
					tnode* selectionnoswap = selection;



					//::reverse.print();
					if (selection->data == 18) {
						bool c = 1;
					}

					if (value > n) {

					}
					else {
						while (!stopswapdown) {
							//calculate sibling
							rangemid = rangeup + rangedown;
							rangemid = rangemid / 2;
							if (selection->lr == 0) {
								sibling = selection->parent->child2;
							}
							if (selection->lr == 1) {
								sibling = selection->parent->child1;
							}
							//check if terminating
							if (inleafposition) { //we might not want to swap here
								stopswapdown = 1;
								//::reverse.print();
								if (sibling->child1 != NULL) { //sibling is not a leaf, then it has at most two descendents
									if (value != rangedown) {// if value is rangedown it is already in the right position
										if (value == rangeup) {
											if (sibling->child2->child1 == NULL) {
												selectionswap = sibling->child2;
												swapdown(selection, 0);
												downlevels++;
												if (::display_level > ::swap_level) {
													cout << value << " moving right to " << rangeup << endl;
												}
											}
											else inleafposition = 0;
										}
										else {
											selectionswap = sibling->child1;
											swapdown(selection, 1);
											downlevels++;

											if (::display_level > ::swap_level) {
												cout << value << " moving left to " << rangeup - 1 << endl;
											}
										}
									}
									else {
										if (selection->lr == 1) {
											if (rangeup - rangedown == 3) {
												//::reverse.print();
												selection->parent->child1 = selection;
												sibling->lr = 1;
												selection->parent->child2 = sibling;
												selection->lr = 0;
												downlevels++;
												if (::display_level > ::swap_level) {
													cout << selection->data << " CASE A2 swapping left with sibling " << sibling->data << endl;
												}
											}
											if (rangeup - rangedown == 2) {
												selectionswap = sibling->child1;
												swapdown(selection, 1);
												downlevels++;
												if (::display_level > ::swap_level) {
													cout << value << " CASE A3 moving left to " << rangeup << endl;
												}
											}
											//not sure if this case can happen
										}
										if (rangeup - rangedown == 1) {
											selectionswap = sibling->child1;
											swapdown(selection, 1);
											downlevels++;
											if (::display_level > ::swap_level) {
												cout << value << " CASE A1 moving left to " << rangeup << endl;
											}
										}
									}
								}
								else {
									if ((selection->lr == 1) && (value == rangedown)) {
										selection->parent->child1 = selection;
										sibling->lr = 1;
										selection->parent->child2 = sibling;
										selection->lr = 0;
										selectionswap = sibling;
										downlevels++;
										if (::display_level > ::swap_level) {
											cout << value << "CASE B swapping left with sibling " << sibling->data << endl;
										}
									}
									else {
										if ((selection->lr == 0) && (value == rangeup)) {
											selection->parent->child2 = selection;
											sibling->lr = 0;
											selection->parent->child1 = sibling;
											selection->lr = 1;
											selectionswap = sibling;
											downlevels++;
											if (::display_level > ::swap_level) {
												cout << selection->data << "CASE C swapping right with sibling " << sibling->data << endl;
											}
										}
									}

								}
							}
							else {
								selection2 = sibling;
								if (firstlevelexception == 2) {
									if (ceil(rangemid) <= value) {
										selectionswap = selection2->child1;
										selectionnoswap = selection2->child2;
										swapdown(selection, 1);

										rangedown = ceil(rangemid);
										downlevels++;
										if (::display_level > ::swap_level) {
											cout << selection->data << " moving right " << rangedown << "to" << rangeup << endl;
										}
										//::reverse.print();
									}
									else {
										selectionswap = selection2->child2;
										selectionnoswap = selection2->child1;
										swapdown(selection, 0);

										rangeup = ceil(rangemid) - 1;
										downlevels++;
										if (::display_level > ::swap_level) {
											cout << selection->data << " moving left " << rangedown << "to" << rangeup << endl;
										}
										//::reverse.print();
									}
								}
								else {
									if (firstlevelexception == 1) {
										selectionswap = selection2->child1;
										selectionnoswap = selection2->child2;
										swapdown(selection, 1);
										firstlevelexception = 2;

									}
									else {
										selectionswap = selection2->child2;
										selectionnoswap = selection2->child2;
										swapdown(selection, 0);
										firstlevelexception = 2;

									}
									if (ceil(rangemid) <= value) {
										rangedown = ceil(rangemid);
										downlevels++;
										if (::display_level > ::swap_level) {
											cout << selection->data << " moving right " << rangedown << "to" << rangeup << endl;
										}
										//::reverse.print();
									}
									else {
										rangeup = ceil(rangemid) - 1;
										downlevels++;
										if (::display_level > ::swap_level) {
											cout << selection->data << " moving left " << rangedown << "to" << rangeup << endl;
										}
										//::reverse.print(); 
									}
								}

								if (selectionswap->child1 == NULL || selectionnoswap->child1 == NULL) {
									inleafposition = 1;
								}
							}
							//if(rangeup < value || rangedown > value) //outside range
							//calculate
							//find new swapping location

						}


						downlevels--;
						while (downlevels > 0) {//main loop
							downlevels--;
							bool g = swapup(selectionswap, f);
							//::reverse.print();
							if (::display_level > ::swap_level) {
								cout << " moving " << selectionswap->data << "upwards" << endl;
							}
							//f = g.thecnf;
						}
						//::reverse.print();
					}
					if (endexcept) {
						swapend(selectionswap, enddir);
					}
					else {
						bool downswapdir2;
						while (!reverseswaps.empty()) {
							downswapdir2 = 0;
							if (reverseswaps.top() == 0) {
								downswapdir2 = 1;
							}
							swapdown(selectionswap, downswapdir2);
							if (::display_level > ::swap_level) {
								cout << " moving " << selectionswap->data << "downwards" << endl;
							}
							//::reverse.print();
							reverseswaps.pop();
						}
					}



					//swap up same number of levels


					//finally swap down
					if (endexcept) {
						selection = selectionswap->parent;
					}
					else{
					selection = selectionswap;
					}
					//selectpos.pop();
				}
					if (::display_level > ::tree_levelpswap) {
						::reverse.print();
						//getchar();
					}
				selectpos.top().tries = 2;
			}
		}
	}
	return;
}

void swappingpair(int n, Cnf f, int a, int b) {
	bool inpos = 0;
		inpos = 1; //this will become false if any leaf is in the wrong position
		tnode* selection = ::reverse.source;
		int rangedown = 1; //the currently selected node has a range of positions
		int rangeup = n;
		stack<swapselcombo> selectpos; //swapselcombo
		selectpos.push(swapselcombo(rangedown, rangeup + 2, 0, 0));
		if (display_level >= endexc_level) {
			cout << "pushing excp" << rangedown << " " << rangeup + 2 << endl;
		}
		selectpos.push(swapselcombo(rangedown, rangeup, 0, 0));
		bool isselectionaleaf = 0;
		bool endexcept = 0;
		while (!isselectionaleaf) { //this traverses all nodes
			isselectionaleaf = 1;

			//recalculate the ranges
			rangedown = selectpos.top().lbound;
			rangeup = selectpos.top().ubound;
			float rangemid = (rangedown + rangeup);
			rangemid = rangemid / 2;
			int tries = selectpos.top().tries;
			if (endexcept) {

			}
			if (a<ceil(rangemid)) {
				if (selection->child1 != NULL) {
					isselectionaleaf = 0;
					selectpos.top().tries++;

					if (endexcept) {}
					else {
						if (::display_level > ::swap_level) {
							cout << "moving left" << endl;
						}
						selection = selection->child1;
						rangeup = ceil(rangemid) - 1;
						selectpos.push(swapselcombo(rangedown, rangeup, 0, 0));
					}
				}
			}
			else {
				if (a<=n) {
					if (selection->child2 != NULL) {
						isselectionaleaf = 0;
						selectpos.top().tries++;

						if (endexcept) {}
						else {
							if (::display_level > ::swap_level) {
								cout << "moving right" << endl;
							}
							selection = selection->child2;
							rangedown = ceil(rangemid);
							selectpos.push(swapselcombo(rangedown, rangeup, 0, 0));
						}
					}
				}
				else {
					if (a>n) {
						isselectionaleaf = 0;
						if (::display_level > ::swap_level) {
							cout << "moving up" << endl;
						}
						if (selection->parent != NULL) {
							selection = selection->parent;
						}
						else {
							endexcept = 1;
						}
						isselectionaleaf = 0;
						selectpos.pop();
					}
				}
			}
			bool enddir = 0;
			if (endexcept && (!selectpos.empty())) { //new code to deal with endlits
				int endvalue;

				if (a==n+1) {
					endvalue = ::reverse.endlit1;
				}
				else {
					endvalue = ::reverse.endlit2;
					enddir = 1;
				}

				if (::display_level > ::endexc_level) {
					cout << "found endleaf with data " << endvalue;
				}
				int enddata = endvalue;

				endvalue = b;
				if (::display_level > ::endexc_level) {
					cout << "and value " << endvalue << endl;
				}
				if (endvalue > n) {
					if ((a == n + 1) && (endvalue == n + 2)) {
						::reverse.endlit1 = ::reverse.endlit2;
						::reverse.endlit2 = enddata;
						return;

					}
					else {
						if ((a == n + 2) && (endvalue == n + 1)) {
							::reverse.endlit2 = ::reverse.endlit1;
							::reverse.endlit1 = enddata;
							return;
						}
					}
				}
				else {
					rangeup = n;
					rangedown = 1;
					//put literal in child 3 position
					//perform clauseshift
					//now next swapdown puts it in realtree and subtree in child3 position
					//however remember to swap out the poor subtree in child3 position on the way back up
					//end by
					selection = new tnode(enddata);
					::reverse.source->child3 = selection;
					selection->parent = ::reverse.source;
					rangemid = rangeup + rangedown;
					rangemid = rangemid / 2;
					tnode* temp;
					if (ceil(rangemid) <= endvalue) {
						swapend(::reverse.source->child1, enddir);
						rangedown = ceil(rangemid);
					}
					else {
						swapend(::reverse.source->child2, enddir);
						rangeup = ceil(rangemid) - 1;
					}
					//sameendstuff as later
					isselectionaleaf = 1;
				}

			}


			if (isselectionaleaf) {



				int value = selection->data;
				value = b;
				int firstlevelexception = 2;
				stack<bool> reverseswaps;
				bool inleafposition = 1;
				tnode* selection2 = selection;
				//getchar();


				if (::display_level > ::swap_level) {
					cout << "found leaf with data " << selection->data << "and value " << value << endl;
				}
				if (value != selectpos.top().lbound || value != selectpos.top().ubound) {
					if (!endexcept) {
						rangeup = selectpos.top().ubound;
						rangedown = selectpos.top().lbound;
						inpos = false;
						//now we have found a leaf to swap
						// here we can use value to find the swapping position
						stack<swapselcombo> selectposcopy = selectpos;

						if (selection->lr == 0) {
							firstlevelexception = 0;
						}
						else {
							firstlevelexception = 1;
						}

						if (::display_level > ::swap_level) {
							cout << selection->data << "not in range " << rangedown << "to" << rangeup << endl;
						}
						bool notinrange = 1;
						inleafposition = 1;
						selection2 = selection;
						while (notinrange) { //the loop for the first push up
							selectposcopy.pop();// this means bounds will be for parent of selection

							if (selectposcopy.top().lbound <= value && selectposcopy.top().ubound >= value) {
								notinrange = 0;
								if (::display_level > ::swap_level) {
									cout << selection->data << "is in the right range " << selectposcopy.top().lbound << "to" << selectposcopy.top().ubound << endl;
								}
								//::reverse.print();
								if (value > n) {
									bool b;
									if (value == n + 1) {
										tnode* thirdnde = new tnode(::reverse.endlit1);
										::reverse.source->child3 = thirdnde;
										thirdnde->parent = ::reverse.source;
										b = swapend(selection, 0);

									}
									else {
										tnode* thirdnde = new tnode(::reverse.endlit2);
										::reverse.source->child3 = thirdnde;
										thirdnde->parent = ::reverse.source;
										b = swapend(selection, 1);

									}
									if (!b) {
										selection = selection->parent->child1;
									}
									else {
										selection = selection->parent->child2;
									}
								}

							}
							else {

								if (::display_level > ::swap_level) {
									cout << selection->data << "not in range " << selectposcopy.top().lbound << "to" << selectposcopy.top().ubound << endl;
								}
								if (selection->lr == 0) {
									firstlevelexception = 0;
								}
								else {
									firstlevelexception = 1;
								}
								bool g;
								if (selection->parent->parent != NULL) {
									g = swapup(selection, f);
									reverseswaps.push(g);
								}


								inleafposition = 0;

								selection2 = selection->parent;

								//::reverse.print();

							}
						}
						rangeup = selectposcopy.top().ubound;
						rangedown = selectposcopy.top().lbound;

					}
					else
					{
						inleafposition = 0;
					}
					//now swapdown 
					int downlevels = 0;
					bool downswapdir = 0;
					bool stopswapdown = 0;



					tnode* sibling = selection;
					tnode* selectionswap = selection;
					tnode* selectionnoswap = selection;



					//::reverse.print();
					if (selection->data == 18) {
						bool c = 1;
					}

					if (value > n) {

					}
					else {
						while (!stopswapdown) {
							//calculate sibling
							rangemid = rangeup + rangedown;
							rangemid = rangemid / 2;
							if (selection->lr == 0) {
								sibling = selection->parent->child2;
							}
							if (selection->lr == 1) {
								sibling = selection->parent->child1;
							}
							//check if terminating
							if (inleafposition) { //we might not want to swap here
								stopswapdown = 1;
								//::reverse.print();
								if (sibling->child1 != NULL) { //sibling is not a leaf, then it has at most two descendents
									if (value != rangedown) {// if value is rangedown it is already in the right position
										if (value == rangeup) {
											if (sibling->child2->child1 == NULL) {
												selectionswap = sibling->child2;
												swapdown(selection, 0);
												downlevels++;
												if (::display_level > ::swap_level) {
													cout << value << " moving right to " << rangeup << endl;
												}
											}
											else inleafposition = 0;
										}
										else {
											selectionswap = sibling->child1;
											swapdown(selection, 1);
											downlevels++;

											if (::display_level > ::swap_level) {
												cout << value << " moving left to " << rangeup - 1 << endl;
											}
										}
									}
									else {
										if (selection->lr == 1) {
											if (rangeup - rangedown == 3) {
												//::reverse.print();
												selection->parent->child1 = selection;
												sibling->lr = 1;
												selection->parent->child2 = sibling;
												selection->lr = 0;
												downlevels++;
												if (::display_level > ::swap_level) {
													cout << selection->data << " CASE A2 swapping left with sibling " << sibling->data << endl;
												}
											}
											if (rangeup - rangedown == 2) {
												selectionswap = sibling->child1;
												swapdown(selection, 1);
												downlevels++;
												if (::display_level > ::swap_level) {
													cout << value << " CASE A3 moving left to " << rangeup << endl;
												}
											}
											//not sure if this case can happen
										}
										if (rangeup - rangedown == 1) {
											selectionswap = sibling->child1;
											swapdown(selection, 1);
											downlevels++;
											if (::display_level > ::swap_level) {
												cout << value << " CASE A1 moving left to " << rangeup << endl;
											}
										}
									}
								}
								else {
									if ((selection->lr == 1) && (value == rangedown)) {
										selection->parent->child1 = selection;
										sibling->lr = 1;
										selection->parent->child2 = sibling;
										selection->lr = 0;
										selectionswap = sibling;
										downlevels++;
										if (::display_level > ::swap_level) {
											cout << value << "CASE B swapping left with sibling " << sibling->data << endl;
										}
									}
									else {
										if ((selection->lr == 0) && (value == rangeup)) {
											selection->parent->child2 = selection;
											sibling->lr = 0;
											selection->parent->child1 = sibling;
											selection->lr = 1;
											selectionswap = sibling;
											downlevels++;
											if (::display_level > ::swap_level) {
												cout << selection->data << "CASE C swapping right with sibling " << sibling->data << endl;
											}
										}
									}

								}
							}
							else {
								selection2 = sibling;
								if (firstlevelexception == 2) {
									if (ceil(rangemid) <= value) {
										selectionswap = selection2->child1;
										selectionnoswap = selection2->child2;
										swapdown(selection, 1);

										rangedown = ceil(rangemid);
										downlevels++;
										if (::display_level > ::swap_level) {
											cout << selection->data << " moving right " << rangedown << "to" << rangeup << endl;
										}
										//::reverse.print();
									}
									else {
										selectionswap = selection2->child2;
										selectionnoswap = selection2->child1;
										swapdown(selection, 0);

										rangeup = ceil(rangemid) - 1;
										downlevels++;
										if (::display_level > ::swap_level) {
											cout << selection->data << " moving left " << rangedown << "to" << rangeup << endl;
										}
										//::reverse.print();
									}
								}
								else {
									if (firstlevelexception == 1) {
										selectionswap = selection2->child1;
										selectionnoswap = selection2->child2;
										swapdown(selection, 1);
										firstlevelexception = 2;

									}
									else {
										selectionswap = selection2->child2;
										selectionnoswap = selection2->child2;
										swapdown(selection, 0);
										firstlevelexception = 2;

									}
									if (ceil(rangemid) <= value) {
										rangedown = ceil(rangemid);
										downlevels++;
										if (::display_level > ::swap_level) {
											cout << selection->data << " moving right " << rangedown << "to" << rangeup << endl;
										}
										//::reverse.print();
									}
									else {
										rangeup = ceil(rangemid) - 1;
										downlevels++;
										if (::display_level > ::swap_level) {
											cout << selection->data << " moving left " << rangedown << "to" << rangeup << endl;
										}
										//::reverse.print();
									}
								}

								if (selectionswap->child1 == NULL || selectionnoswap->child1 == NULL) {
									inleafposition = 1;
								}
							}
							//if(rangeup < value || rangedown > value) //outside range
							//calculate
							//find new swapping location

						}


						downlevels--;
						while (downlevels > 0) {//main loop
							downlevels--;
							bool g = swapup(selectionswap, f);
							//::reverse.print();
							if (::display_level > ::swap_level) {
								cout << " moving " << selectionswap->data << "upwards" << endl;
							}
							//f = g.thecnf;
						}
						//::reverse.print();
					}
					if (endexcept) {

						swapend(selectionswap, enddir);


					}
					else {
						bool downswapdir2;
						while (!reverseswaps.empty()) {
							downswapdir2 = 0;
							if (reverseswaps.top() == 0) {
								downswapdir2 = 1;
							}
							swapdown(selectionswap, downswapdir2);
							if (::display_level > ::swap_level) {
								cout << " moving " << selectionswap->data << "downwards" << endl;
							}
							//::reverse.print();
							reverseswaps.pop();
						}
					}



					//swap up same number of levels


					//finally swap down
					if (endexcept) {
						selection = selectionswap->parent;
					}
					else {
						selection = selectionswap;
					}
					//selectpos.pop();
				}
				if (::display_level > ::tree_levelpswap) {
					::reverse.print();
					//getchar();
				}
				selectpos.top().tries = 2;
			}


		}
	return;
}

tree lineartree(tree g, bool r , int lb, int ub ) {
	if (ub-lb<2) {
		return g; // already log depth
	}

	float m = (lb + ub);
	m = m / 2;
	int mint = ceil(m);
	tree g1(g.source->child1); //the left tree
	tree g2(g.source->child2); //the right tree

	g1 = lineartree(g1, 0, lb, mint-1);
	g2 = lineartree(g2, 1, mint, ub);

	//float noofinternals = (g.depth - 2);
	//float halfinternals = (noofinternals / 2);
	//g1.depth = floor(halfinternals) + 1;
	//g2.depth = ceil(halfinternals) + 1;
	//g.depth = max(g1.depth, g2.depth) + 1;
	//g.depth = max(g1.depth, g2.depth) + 1;
	//merge the two cnfs and return
	int reps;
	if (!r) {
		// we will add ceil n / 2 Tseitin variables to g2
		reps= ub - mint;
		for (int i = 0; i < reps; i++) {

			int lit1 = g.source->data;
			int lit2 = g.source->child2->child2->data;
			int lit3 = g.source->child2->child1->data;
			int lit4 = g.source->child1->data;
			int elim = g.source->child2->data;

			::Clauseshift(lit1, lit2, lit3, lit4, elim);

			g.treeshiftl();
		}


	}
	else {
		reps = mint-lb-1;
		for (int i = 0; i < reps; i++) {

			int lit1 = g.source->data;
			int lit2 = g.source->child1->child1->data;
			int lit3 = g.source->child1->child2->data;
			int lit4 = g.source->child2->data;
			int elim = g.source->child1->data;

			::Clauseshift(lit1, lit2, lit3, lit4, elim);

			g.treeshiftr();


		}
	}

	return g;
}

void finalequiv(int n, std::vector<int> invector) {
	ofstream prooffile;
	tnode* select = ::reverse.source;
	while (select->child1 != NULL) {
		select = select->child1;
	}
	prooffile.open("formula.drat", ios::app);
	int l2 = invector[0];
	int r2 = invector[1];
	int u2 = 2 * n-2;
	int l1 = select->data;
	int r1 = select->parent->child2->data;
	int u1 = select->parent->data;

	l1 = ::extvariables[l1 - 1];
	l2 = ::extvariables[l2 - 1];
	r1 = ::extvariables[r1 - 1];
	r2 = ::extvariables[r2 - 1];
	u1 = ::extvariables[u1 - 1];
	u2 = ::extvariables[u2 - 1];

	bool flip = 0;
	Clause A1 = Clause(-l1, -u1, u2, 0);
	Clause A2 = Clause(-l1, u1, -u2, 0);
	Clause A3 = Clause(l1, u1, -u2, 0);
	Clause A4 = Clause(l1, u1, -u2, 0);
	Clause I1 = Clause(-u1, u2, 0, 0);
	Clause I2 = Clause(u1, -u2, 0, 0);
	if ((l1 == l2) ^ (r1 == r2)) {
		A1 = Clause(-l1, u1, u2, 0);
		A2 = Clause(-l1, u1, u2, 0);
		A3 = Clause(l1, -u1, -u2, 0);
		A4 = Clause(l1, -u1, -u2, 0);
		I1 = Clause(u1, u2, 0, 0);
		I2 = Clause(-u1, -u2, 0, 0);
		flip = 1;
	}
	{
		ATA(A1);
		for (int i = 0; i < 4; i++) {
			if (A1.lit[i] == 0) {
				break;
			}
			prooffile << A1.lit[i] << " ";
		}
		prooffile << 0 << "\n";
		ATA(A2);
		for (int i = 0; i < 4; i++) {
			if (A2.lit[i] == 0) {
				break;
			}
			prooffile << A2.lit[i] << " ";
		}
		prooffile << 0 << "\n";
		ATA(A3);
		for (int i = 0; i < 4; i++) {
			if (A3.lit[i] == 0) {
				break;
			}
			prooffile << A3.lit[i] << " ";
		}
		prooffile << 0 << "\n";
		ATA(A4);
		for (int i = 0; i < 4; i++) {
			if (A4.lit[i] == 0) {
				break;
			}
			prooffile << A4.lit[i] << " ";
		}
		prooffile << 0 << "\n";

		ATA(I1);
		for (int i = 0; i < 4; i++) {
			if (I1.lit[i] == 0) {
				break;
			}
			prooffile << I1.lit[i] << " ";
		}
		prooffile << 0 << "\n";


		ATA(I2);
		for (int i = 0; i < 4; i++) {
			if (I2.lit[i] == 0) {
				break;
			}
			prooffile << I2.lit[i] << " ";
		}
		prooffile << 0 << "\n";
	}//printing to file
	for (int i = 2; i < n-2; i++ ) {
		select = select->parent;
		int r1 = select->parent->child2->data;
		int l2 = 2 * n + i - 4;
		int l1 = select->data;
		int r2 = invector[i];
		int u1 = select->parent->data;
		int u2 = 2 * n + i-3;

		l1 = ::extvariables[l1 - 1];
		l2 = ::extvariables[l2 - 1];
		r1 = ::extvariables[r1 - 1];
		if (r2 > 0) {
			r2 = ::extvariables[abs(r2) - 1];
		}
		else {
			r2 = -::extvariables[abs(r2) - 1];
		}
		u1 = ::extvariables[u1 - 1];
		u2 = ::extvariables[u2 - 1];

		A1 = Clause(-l1, -u1, u2, 0);
		A2 = Clause(-l1, -u1, u2, 0);
		A3 = Clause(l1, u1, -u2, 0);
		A4 = Clause(l1, u1, -u2, 0);
		I1 = Clause(u1, -u2, 0, 0);
		I2 = Clause(-u1, u2, 0, 0);
		if ((flip) ^ (r1 != r2)) {
			A1 = Clause(-l1, u1, u2, 0);
			A2 = Clause(-l1, u1, u2, 0);
			A3 = Clause(l1, -u1, -u2, 0);
			A4 = Clause(l1, -u1, -u2, 0);
			I1 = Clause(u1, u2, 0, 0);
			I2 = Clause(-u1, -u2, 0, 0);
			flip = 1;
		}
		else {
			flip = 0;
		}
		if (::display_level > ::swap_level) {
			cout << "induction level" << i << endl;
		}
		{
			ATA(A1);
			for (int i = 0; i < 4; i++) {
				if (A1.lit[i] == 0) {
					break;
				}
				prooffile << A1.lit[i] << " ";
			}
			prooffile << 0 << "\n";
			ATA(A2);
			for (int i = 0; i < 4; i++) {
				if (A2.lit[i] == 0) {
					break;
				}
				prooffile << A2.lit[i] << " ";
			}
			prooffile << 0 << "\n";
			ATA(A3);
			for (int i = 0; i < 4; i++) {
				if (A3.lit[i] == 0) {
					break;
				}
				prooffile << A3.lit[i] << " ";
			}
			prooffile << 0 << "\n";
			ATA(A4);
			for (int i = 0; i < 4; i++) {
				if (A4.lit[i] == 0) {
					break;
				}
				prooffile << A4.lit[i] << " ";
			}
			prooffile << 0 << "\n";

			ATA(I1);
			for (int i = 0; i < 4; i++) {
				if (I1.lit[i] == 0) {
					break;
				}
				prooffile << I1.lit[i] << " ";
			}
			prooffile << 0 << "\n";


			ATA(I2);
			for (int i = 0; i < 4; i++) {
				if (I2.lit[i] == 0) {
					break;
				}
				prooffile << I2.lit[i] << " ";
			}
			prooffile << 0 << "\n";
		}//printing to file
	}

	A1 = Clause(invector[n-1] , invector[n - 2], 0, 0);
	A2 = Clause(invector[n-1]  , -invector[n - 2], 0, 0);
	A3 = Clause(-invector[n-1], invector[n - 2], 0, 0);
	A4 = Clause(-invector[n-1], -invector[n - 2], 0, 0);
	I1 = Clause(-invector[n-1], 0 , 0, 0);
	I2 = Clause(invector[n-1], 0, 0, 0);
	ATA(A1);
	for (int i = 0; i < 4; i++) {
		if (A1.lit[i] == 0) {
			break;
		}
		prooffile << A1.lit[i] << " ";
	}
	prooffile << 0 << "\n";
	ATA(A2);
	for (int i = 0; i < 4; i++) {
		if (A2.lit[i] == 0) {
			break;
		}
		prooffile << A2.lit[i] << " ";
	}
	prooffile << 0 << "\n";
	ATA(A3);
	for (int i = 0; i < 4; i++) {
		if (A3.lit[i] == 0) {
			break;
		}
		prooffile << A3.lit[i] << " ";
	}
	prooffile << 0 << "\n";
	ATA(A4);
	for (int i = 0; i < 4; i++) {
		if (A4.lit[i] == 0) {
			break;
		}
		prooffile << A4.lit[i] << " ";
	}
	prooffile << 0 << "\n";

	ATA(I1);
	for (int i = 0; i < 4; i++) {
		if (I1.lit[i] == 0) {
			break;
		}
		prooffile << I1.lit[i] << " ";
	}
	prooffile << 0 << "\n";


	ATA(I2);
	for (int i = 0; i < 4; i++) {
		if (I2.lit[i] == 0) {
			break;
		}
		prooffile << I2.lit[i] << " ";
	}
	prooffile << 0 << "\n";

	Clause empty = Clause(0, 0, 0, 0);
	ATA(empty);
	prooffile << 0 << "\n";
	prooffile.close();

}


int main (int argc, char** argv) {
	int n = 10;
        int seed = 123456;

        if (argc > 1) n    = atoi (argv[1]);
        if (argc > 2) seed = atoi (argv[2]);

	srand(seed);
	if (n < 4) {
		cout << "n is too small";
		return 0;
	}
	//cout << "Hello World" << endl;
	if (remove("formula.drat") != 0)
	  // perror("Could not delete file: formula.drat")
	  ;
	else
	  //	        puts("File successfully deleted")
	  ;
	if (remove("formula.cnf") != 0)
	  // perror("Could not delete file: formula.cnf")
	  ;
	else
	  // puts("File successfully deleted")
	  ;

	//std::srand(unsigned(std::time(0)));
	std::vector<int> myvector;

	// set some values:
	for (int i = 1; i<n+1; ++i) myvector.push_back(i); // 1 2 3 4 5 6 7 8 9

	//ER stuff in main
	for (int i = 1; i<=3 * n - 6; ++i) ::extvariables.push_back(i); // 1 2 3 4 5 6 7 8 9
	::maxextvar = 3 * n - 6;
	::ERproofonly = 1;

	// using myrandom:
	std::random_shuffle(myvector.begin(), myvector.end(), myrandom);

#if 0
	// print out content:
	std::cout << "myvector contains:";
	for (std::vector<int>::iterator it = myvector.begin(); it != myvector.end(); ++it)
		std::cout << ' ' << *it;

	std::cout << '\n';
#endif

	//getchar();
	double duration;
	std::clock_t start;

	start = std::clock();
	//	cout << "creating CNF.txt" << endl;

	//Clause C = Clause(-1, 2, 3, 4);
	int negativelit = myrandom(n);
	Cnf P= Parity(n-2, myvector, negativelit);
	//C.Display();
	::maxextvar = 3 * n - 6;
	std::vector<int> revvector= myvector;

	for (int i = 1; i < n+1; i++) {
		revvector[myvector[i-1]-1] = i;
	}

#if 0
	std::cout << "revvector contains:";
	for (std::vector<int>::iterator it = revvector.begin(); it != revvector.end(); ++it)
		std::cout << ' ' << *it;

	std::cout << '\n';
#endif

	ofstream cnffile;
	cnffile.open("formula.cnf", ios::app);
	cnffile << "p cnf " << 3 * n -6 << " " << P.cspace << "\n";
	cnffile.close();
	::f = P;
	//::f.Display();
	::f.Print();
	duration = (std::clock() - start) / (double)CLOCKS_PER_SEC;
	std::cout << "time for constructing CNF:" << duration << endl;
	//::reverse.print();
#ifndef CNF_ONLY

	bool skipprvr = 0;

	//getchar();
	if (!skipprvr){
	  //		cout << "creating formula.drat" << endl;
		std::clock_t start2;
		start2 = std::clock();
		::reverse = rebalance(::reverse, 0);
		//		::reverse.print();
		//getchar();

		swapping(n - 2, f, revvector);
		//		::reverse.print();
		//getchar();
		lineartree(::reverse, 0, 1, n - 2);
		//getchar();
		myvector[negativelit] = -myvector[negativelit];
		finalequiv(n, myvector);

		::myfile.close();
		duration = (std::clock() - start2) / (double)CLOCKS_PER_SEC;
		cout << "time elapsed " << duration << endl;
		cout << "number of ATA lines " << ::ATAsize << endl;
		cout << "number of RATA lines " << ::RATAsize << endl;
		cout << "number of ATE lines " << ::ATEsize << endl;
		cout << "number of RATE lines " << ::RATEsize << endl;
		cout << " n " << "\t" << "#vars " << "\t" << "#c " << "\t" << "#lines" << "\t" << "#add" << "\t" << "#del" << "\t" << endl;
		cout << n << "\t" << ::maxextvar << "\t" << 8 * (n - 2) << "\t" << ::proofsize << "\t" << ::ATAsize + ::RATAsize << "\t" << ::ATEsize + ::RATEsize << endl;

		ofstream stats;
		stats.open("stats.txt", ios::app);
		stats << " n " << "\t" << "#vars " << "\t" << "#c " << "\t" << "#lines" << "\t" << "#add" << "\t" << "#del" << "\t" <<  "time elapsed "  << endl;
		stats << n << "\t" << ::maxextvar << "\t" << 8 * (n - 2) << "\t" << ::proofsize << "\t" << ::ATAsize + ::RATAsize << "\t" << ::ATEsize + ::RATEsize << "\t" <<  duration << endl;
		//		cnffile.close();
//		getchar();
	}
#endif
}
