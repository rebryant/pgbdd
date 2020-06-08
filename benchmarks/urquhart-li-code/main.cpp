#include "generate.h"

int main(int argc, char *argv[]) {
	CGenerator Gen;
	Gen.Init(argc,argv);
	Gen.Run();
	Gen.Stop();
	return 0;
}




