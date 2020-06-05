#pragma once
struct pnode {
	int input;
	int output;
	pnode *next;

	pnode(int x, int y) {
		input = x;
		output = y;
		next = nullptr;
	}

	pnode() {
		input = 0;
		output = 0;
		next = nullptr;
	};
};

struct permutation {
	pnode * source;

	void append(int x, int y) {
		pnode *temp1 = new pnode(x,y);
		temp1->next = source;
		source = temp1;
		size++;
	}

	void proaddswap(int x, int y) {
		if (x == y){
			addtriv();
			return;
		}
		pnode *current = new pnode();
		current = source;
		bool flagx = 0;
		bool flagy = 0;
		while (current != nullptr) {
			if (current->output == x) {
				flagx = 1;
				current->output = y;
			}
			else {
				if (current->output == y) {
					flagy = 1;
					current->output = x;
				}
			}
			current=current->next;

		}
		if (flagx == 0) {
			append(x, y);
		}
		if (flagy == 0) {
			append(y, x);
		}
	};

	void preadd(int, int y);

	permutation procompose(permutation p);
	permutation precompose(permutation p);
	permutation inverse ();

	int size;

	std::vector<int> outputvector() {
		pnode *current = new pnode();
		current=source;
		int tempsize = 0;
		while (current != nullptr) {
			current = current->next;
			tempsize++;
		}
		size = tempsize;
		std::vector<int> outvector;
		int vctrrng=0;
		current = source;
		while (current != nullptr) {
			int difference = current->input - vctrrng;
			while (difference > 0) {
				outvector.push_back(0);
				difference--;
			}
			current = current->next;
			outvector[(current->input) - 1] = current->output;
		}

		return outvector;
	};

	void addtriv ();
	bool validate ();
};

struct tnode {
	int data;
	bool lr;
	//int depth;
	tnode *child1;
	tnode *child2;
	tnode *child3;
	tnode *parent;
	tnode(int i) {
		data = i;
		lr = 0;
		child1 = NULL;
		child2 = NULL;
		child3 = NULL;
		parent = NULL;
	};
	void printrt(int dp) {

		std::cout << data; // print label after last label
		if (child1 != NULL) {
			std::cout << "_\t_";
			child1->printrt(dp+1);
		}
		else { std::cout << "\t"; }
		if (child2 != NULL) {
			std::cout << std::endl;
			for (int i = 0; i < dp; i++) {
				std::cout << " \t";
			}
			if (dp > 0) {
				std::cout << " \\";
			}
			std::cout << std::endl;
			for (int i = 1; i < dp+1; i++) {
				std::cout << "\t";
			}
				std::cout << "   -\t";
			std::cout << "_";
			child2->printrt(dp+1);
		}
	};
};

struct Cnftnodepair {
	tnode* nodestar;
	Cnf form;
};


struct tree {
	tnode * source;
	int depth;
	int endlit1;
	int endlit2;
	tree(int i) {
		tnode *temp = new tnode(i);
		source = temp;
		depth = 1;
		endlit1 = 0;
		endlit2 = 0;
	};

	tnode* cmancestor(tnode* a, tnode* b) {
		stack<tnode*> astk;
		stack<tnode*> bstk;
		tnode* current;
		current = a;
		while (current != nullptr) {
			astk.push(current);
		}
		current = b;
		while (current != nullptr) {
			bstk.push(current);
		}

		while (astk.top() == bstk.top()) {
			current = astk.top();
			astk.pop();
			bstk.pop();
		}

		return current;

	}

	void print() {
		source->printrt(0);
		cout<<endl;
	};

	tree(tnode* s) {
		source = s;
//		s->parent;
	};

	tnode* IntFindNode(int i, tnode* base) { // find node with data i;
		if (base->data == i) {
			return base;
		}
		tnode* q;
		if (base->child1 != NULL) {
			q = IntFindNode(i, base->child1);
			if (q != NULL) {
				return q;
			}
		}
		if (base->child2 != NULL) {
			q = IntFindNode(i, base->child1);
			if (q != NULL) {
				return q;
			}
		}
		return NULL;
	};

	tnode* IntFindNode(int i) {
		return IntFindNode(i, source);
	}


	

	void treeshiftr(tnode* pivot) {
		tnode* elim;
		//first eliminate our node
		elim = pivot->child1;
		//new child1 is grandchild of pivot from elim side
		pivot->child1 = elim->child1;
		elim->child1->parent = pivot;
		

		//elim moves child2 to child 1
		elim->child1 = elim->child2;
		elim->child1->lr = 0;

		//child2 becomes child2 of elim
		pivot->child2->parent = elim;
		elim->child2 = pivot->child2;
		elim->child2->lr = 1;
		
		//elim becimes new child2 of pivot
		pivot->child2 = elim;
		pivot->child2->lr= 1;
		//elim->parent=pivot; but this is already true
	}

	void treeshiftl(tnode* pivot) {
		tnode* elim;
		//first eliminate our node
		elim = pivot->child2;
		//new child2 is grandchild of pivot from elim side
		pivot->child2 = elim->child2;
		pivot->child2->lr = 1;
		elim->child2->parent = pivot;

		//elim moves child1 to child 2
		elim->child2 = elim->child1;
		elim->child2->lr = 1;

		//child1 becomes child1 of elim
		pivot->child1->parent = elim;
		elim->child1 = pivot->child1;
		elim->child1->lr = 0;

		//elim becimes new child1 of pivot
		pivot->child1 = elim;
		pivot->child1->lr = 0;
		//elim->parent=pivot; but this is already true
	}

	void treeshiftr() {
		treeshiftr(source);
	}

	void treeshiftl() {
		tnode* elim;
		treeshiftl(source);

	}


	void ExtendSource(int i, int j, bool dir) {
		tnode *temp1 = new tnode(i);
		tnode *temp2 = new tnode(j);
		
		temp2->child1 = NULL;
		temp2->child2 = NULL; //temp 2 is an added leaf
		temp2->parent = temp1; //temp1 is the new source

		if (dir == 1) {
			source->lr = 0;
			source->parent = temp1;
			temp1->child1 = source;
			temp1->child1->lr=0;
			temp1->child2 = temp2;
			temp1->child2->lr = 1;
			temp1->parent = NULL;
		}
		else{
			source->lr = 1;
			source->parent = temp1;
			temp1->child2 = source;
			temp1->child2->lr = 1;
			temp1->child1 = temp2;
			temp1->child1->lr = 0;
			temp1->parent = NULL;
		}
		source = temp1;
		depth++;
	}
};

struct cnftree {
	Cnf thecnf;
	tree thetree;
};
