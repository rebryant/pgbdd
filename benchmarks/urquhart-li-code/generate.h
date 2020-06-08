#ifndef GENERATE
#define GENERATE
#include "graph.h"

class CGenerator {
private:
	CGraph *G;
	char Output_File[255];
	unsigned int ShowRules;
	void Help(char *name);
	int CheckArguments(char *arg);
public:
	void Init(int argc,char *argv[]);
	void Run();
	void Stop();
};

#endif