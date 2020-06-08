#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/************************ Modifications ***********************
 *
 *  2020-06-08.  Fixed constant character warnings
 *  2020-06-08.  Fixed unitialized value of p
 *
 *
 ************************ Modifications ***********************/



#include "generate.h"

#define NUM_ARG		4
#define ARG_1	 		"-m"
#define ARG_2	 		"-r"
#define ARG_3	 		"-f"
#define ARG_4	 		"-p"

const char *Argument[NUM_ARG]= { ARG_1, ARG_2, ARG_3, ARG_4 };

void CGenerator::Help(char *name) {
	printf("How to use it:\n");
	printf("%s "ARG_1"<m> "ARG_2" "ARG_3"<file name> "ARG_4"<25-75>\n",name);
	printf(ARG_1" -> m value, with m >= 2\n");
	printf(ARG_4" -> m value, with 25 <= p <= 75\n");
	printf(ARG_2" -> Show Rules\n");
	printf(ARG_3" -> File name for output\n");
	exit(-1);
}

int CGenerator::CheckArguments(char *arg)
{
		for(unsigned int i=0;i<NUM_ARG;i++)
			if( strstr(arg,Argument[i])!=NULL)
				return i;
		return -1;
}

void CGenerator::Init(int argc, char *argv[]) {
	char *string, *endptr;
	int i,arg_view[3],Error=0;
	long m = 3;
        long p = 50;
	ShowRules=0;

	arg_view[0]=0;
	arg_view[1]=0;
	arg_view[2]=0;

	if(argc>=2)
	{
		for(i=1;i<argc;i++)
		{
			switch(CheckArguments(argv[i]))
			{
				case 0:
					string=strstr(argv[i],ARG_1);
					string+=2;
					m = strtol(string, &endptr, 10);
					if(m<=1)
						printf(" -> Invalid value for m, m must be >= 2\n");
					else
					{
						printf(" -> Working with value %ld for m\n",m);
						arg_view[0]=1;
					}
					break;

				case 1:
					ShowRules=(strstr(argv[i],ARG_2)!=NULL);
					printf(" -> Showing Rules\n");
					break;

				case 2:
					string=strstr(argv[i],ARG_3);
					if(strcmp(string,ARG_3)==0)
						printf(" -> Missing File Name\n");
					else
					{
						string+=2;
						strcpy(Output_File,string);
						printf(" -> Using File %s\n",Output_File);
						arg_view[1]=1;
					}
					break;

				case 3:
					string=strstr(argv[i],ARG_4);
					string+=2;
					p = strtol(string, &endptr, 10);
					if(p<25 || p>75)
						printf(" -> Invalid value for p, it must be 25 <= p <= 75\n");
					else
					{
						printf(" -> Working with value %ld for p\n",p);
						arg_view[2]=1;
					}
					break;

				default:
					printf("Invalid Argument -> \"%s\"\n",argv[i]);
					break;
			}
		}
		if(arg_view[0] && arg_view[1] && arg_view[2])
			G=new CGraph(m,p);
		else
			Error=1;
	}
	else
		Error=1;

	if(Error) Help(argv[0]);
}

void CGenerator::Run() {
	G->Generate();
	G->Output(Output_File);
	if(ShowRules) G->PrintRules();
}

void CGenerator::Stop() {
	delete G;
}
