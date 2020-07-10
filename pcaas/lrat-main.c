/************************************************************************************[lrat-check.c]
Copyright (c) 2017-2020 Marijn Heule, Randal E. Bryant, Carnegie Mellon University
Last edit: June 1, 2020

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
associated documentation files (the "Software"), to deal in the Software without restriction,
including without limitation the rights to use, copy, modify, merge, publish, distribute,
sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or
substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
**************************************************************************************************/

/* Main function for LRAT checker */

#include <stdlib.h>
#include <stdio.h>
#include <fcntl.h>

#include "stream.h"
/* Defined in lrat.c */
bool check_proof(rio_t *rp_cnf, rio_t *rp_proof, bool is_binary, rio_t *rp_out);


void usage(char *name) {
  printf("Usage: %s (FILE.uratb|FILE1.cnf FILE2.lrat[b])\n", name);
  exit(0);
}

int main (int argc, char** argv) {
  bool ok = true;
  if (argc < 2 || argc > 3)
     usage(argv[0]);
  bool unified = argc == 2;
  rio_t rio_cnf;
  rio_t rio_proof;
  rio_t rio_out;
  rio_t *rp_proof;
  bool is_binary = false;

  rio_initb(&rio_out, STDOUT_FILENO);

  /* Process CNF file */
  int cnf_fd =  open(argv[1], O_RDONLY);
  if (cnf_fd < 0) {
      fprintf(stderr, "Couldn't open input file '%s'\n", argv[1]);
      exit(1);
  }
  rio_initb(&rio_cnf, cnf_fd);

  is_binary = unified || argv[2][strlen(argv[2])-1] == 'b';
  if (unified) {
      rp_proof = NULL;
  } else {
      int proof_fd =  open(argv[2], O_RDONLY);
      if (proof_fd < 0) {
	  fprintf(stderr, "Couldn't open input file '%s'\n", argv[2]);
	  exit(1);
      }
      rp_proof = &rio_proof;
      rio_initb(rp_proof, proof_fd);
  }
  ok = check_proof(&rio_cnf, rp_proof, is_binary, &rio_out) ? 0 : 1;
  close(rio_cnf.rio_fd);
  if (!unified)
      close(rio_proof.rio_fd);  
  close(rio_out.rio_fd);
  return ok;
}
