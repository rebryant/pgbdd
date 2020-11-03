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

#include <stdio.h>
#include <stdlib.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <sys/time.h>

#include "stream.h"

#define DELETED		-1
#define SUCCESS		1
#define FAILED		0
#define CNF		100
#define LRAT		200
#define LRATB           201
#define CLRAT		300

#define BLEN  256



long long added_clauses = 0;
long long deleted_clauses = 0;
long long live_clauses = 0;
long long max_live_clauses = 0;

long long *mask, *intro, now, lastIndex;

int *clsList = NULL;
int clsAlloc, clsLast;
int *table = NULL;
int tableSize, tableAlloc, maskAlloc;
int_list_t *litList = NULL;

rio_t *rp_out;

int  getType   (int* list) { return list[1]; }
int  getIndex  (int* list) { return list[0]; }
int  getLength (int* list) { int i = 2; while (list[i]) i++; return i - 2; }
int* getHints  (int* list) { return list + getLength (list) + 2; }
int  getRATs   (int* list) { int c = 0; while (*list) if ((*list++) < 0) c++; return c; }

int convertLit (int lit)   { return (abs(lit) * 2) + (lit < 0); }

void printClause (int* clause) {
    while (*clause) {
	rio_nprintf(rp_out, BLEN, "%i ", *clause++);
    }
    rio_nprintf(rp_out, BLEN, "0\n"); 
}

int checkRedundancy (int pivot, int start, int *hints, long long thisMask) {
  int res = abs(*hints++);
  if (start > res) {
      rio_nprintf(rp_out, BLEN, "c Assertion failed in checkRedundancy.  start == %d, res = %d\n",
		  start, res);
      return FAILED;
  }

  if (res != 0) {
    while (start < res) {
      if (clsList[start++] != DELETED) {
        int *clause = table + clsList[start-1];
        while (*clause) {
          int clit = convertLit (*clause++);
          if (clit == (pivot^1)) return FAILED; } } }
    if (clsList[res] == DELETED) {
	rio_nprintf(rp_out, BLEN, "c ERROR: using DELETED clause\n");
	rio_nprintf(rp_out, BLEN, "c NOT VERIFIED\n"); 
	return FAILED;
    }
    int flag = 0, *clause = table + clsList[res];
    while (*clause) {
      int clit = convertLit (*clause++);
//      assert (clit < maskAlloc);
      if (clit == (pivot^1)) { flag = 1; continue; }
      if (mask[clit  ] >= thisMask) continue;       // lit is falsified
      if (mask[clit^1] >= thisMask) return SUCCESS; // blocked
      mask[clit] = thisMask; }
    if (flag == 0) return FAILED; }

  while (*hints > 0) {
    if (clsList[*hints] == DELETED) {
      rio_nprintf(rp_out, BLEN, "c ERROR: using DELETED clause\n");
      rio_nprintf(rp_out, BLEN, "c NOT VERIFIED\n"); 
      return FAILED;
    }
    int unit = 0, *clause = table + clsList[*(hints++)];
    while (*clause) {
      int clit = convertLit (*(clause++));
      if (mask[clit] >= thisMask) continue; // lit is falsified
      if (unit != 0) return FAILED;
      unit = clit; }
    if (unit == 0) return SUCCESS;
    if (mask[unit^1] == thisMask) rio_nprintf(rp_out, BLEN, "c WARNING hint already satisfied in lemma with index %lli\n", lastIndex);
    mask[unit^1] = thisMask; }

  if (res == 0) return SUCCESS;
  return FAILED; }

int checkClause (int* list, int size, int* hints) {
  now++;
  int i, j, pivot = convertLit (list[0]);
  int RATs = getRATs (hints + 1);
  for (i = 0; i < size; i++) {
    int clit = convertLit (list[i]);
    if (clit >= maskAlloc) {
      int old = maskAlloc;
      maskAlloc = (clit * 3) >> 1;
//      rio_nprintf(rp_out, BLEN, "c realloc mask to %i\n", maskAlloc);
      mask  = (long long *) realloc (mask,  sizeof (long long) * maskAlloc);
      intro = (long long *) realloc (intro, sizeof (long long) * maskAlloc);
      if (!mask || !intro) { rio_nprintf(rp_out, BLEN, "c Memory allocation failure\n"); return FAILED; }
      for (j = old; j < maskAlloc; j++) mask[j] = intro[j] = 0; }
    mask [clit] = now + RATs; }

  int res = checkRedundancy (pivot, 0, hints, now + RATs);
  if (res  == FAILED) return FAILED;
  if (RATs == 0)      return SUCCESS;

  int start = intro[pivot ^ 1];
  if (start == 0) return SUCCESS;
//  int start = 1;
  while (1) {
    hints++; now++; while (*hints > 0) hints++;
    if (*hints == 0) break;
    if (checkRedundancy (pivot, start, hints, now) == FAILED) return FAILED;
    start = abs(*hints) + 1; }

  while (start <= clsLast) {
    if (clsList[start++] != DELETED) {
      int *clause = table + clsList[start-1];
      while (*clause) {
        int clit = convertLit (*clause++);
        if (clit == (pivot^1)) return FAILED; } } }

  return SUCCESS; }

void addClause (int index, int* literals, int size) {
  if (index >= clsAlloc) {
    int i = clsAlloc;
    clsAlloc = (index * 3) >> 1;
    clsList = (int*) realloc (clsList, sizeof(int) * clsAlloc);
    while (i < clsAlloc) clsList[i++] = DELETED; }

  if (tableSize + size >= tableAlloc) {
    tableAlloc = (tableAlloc * 3) >> 1;
    table = (int*) realloc (table, sizeof (int) * tableAlloc); }

  clsList[index] = tableSize;
  int i; for (i = 0; i < size; i++) {
    int clit = convertLit (literals[i]);
    if (intro[clit] == 0) intro[clit] = index;
    table[tableSize++] = literals[i]; }
  table[tableSize++] = 0;
  clsLast = index;
  added_clauses++;
  live_clauses++;
  if (live_clauses > max_live_clauses)
      max_live_clauses = live_clauses;
}

void deleteClauses (int* list) {
  while (*list) {
    int index = *list++;
    if (clsList[index] == DELETED) {
      rio_nprintf(rp_out, BLEN, "c WARNING: clause %i is already deleted\n", index); }
    clsList[index] = DELETED;
    deleted_clauses++;
    live_clauses--;
  }
}


bool check_proof(rio_t *rp_cnf, rio_t *rp_proof, bool is_binary, rio_t *arg_rp_out) {
  struct timeval start_time, finish_time;
  char err_buf[BLEN];
  int i;
  bool ok = true;

  rp_out = arg_rp_out;
  gettimeofday(&start_time, NULL);
  now = 0, clsLast = 0;
  litList = int_list_new(0);
  
  if (!get_cnf_header(rp_cnf, litList, err_buf, BLEN)) {
      rio_nprintf(rp_out, BLEN, "c Failed to read CNF header: %s\n", err_buf);
      ok = false;
      goto done;
  }
  int nVar = litList->contents[0];
  int nCls = litList->contents[1];

  clsAlloc = nCls * 2;
  clsList  = (int*) malloc (sizeof(int) * clsAlloc);
  for (i = 0; i < clsAlloc; i++) clsList[i] = DELETED;

  tableSize  = 0;
  tableAlloc = nCls * 2;
  table = (int *) malloc (sizeof(int) * tableAlloc);

  maskAlloc = 20 * nVar;
  mask  = (long long*) malloc (sizeof(long long) * maskAlloc);
  intro = (long long*) malloc (sizeof(long long) * maskAlloc);
  for (i = 0; i < maskAlloc; i++) mask[i] = intro[i] = 0;

  int index = 1;
  while (1) {
      if (!get_cnf_clause(rp_cnf, litList, err_buf, BLEN)) {
	  rio_nprintf(rp_out, BLEN, "c Failed reading clause #%d: %s\n", index, err_buf);
	  ok = false;
	  goto done;
      }
      if (litList->count == 0)
	  break;
      addClause (index++, litList->contents, litList->count); 
  }

  rio_nprintf(rp_out, BLEN, "c parsed a formula with %i variables and %i clauses (%zd bytes)\n",
	      nVar, nCls, rp_cnf->byte_cnt);

  /* 
     When CNF and proof are part of unified stream,
     the CNF will be terminated by one or more bytes with value 0.
     Need to skip these bytes to get to start of proof.
     (The actual proof will start with a clause number > 0,
     and so the first proof byte will be nonzero .)
  */
  if (rp_proof == NULL) {
      rp_proof = rp_cnf;
      char buf[BLEN];
      uint8_t byte = 0;
      int rc;
      /* See what type of proof it's going to be */
      rc = rio_read_token(rp_proof, (uint8_t *) buf, BLEN, NULL);
      if (rc == 0) {
	  rio_nprintf(rp_out, BLEN, "c No proof found\n");
	  ok = false;
	  goto done;
      } else if (rc < 0) {
	  rio_nprintf(rp_out, BLEN, "c Error at start of proof: %s\n", err_buf);
	  ok = false;
	  goto done;
      } else if (strcmp(buf, text_text) == 0) {
	  is_binary = false;
      } else if (strcmp(buf, binary_text) == 0) {
	  is_binary = true;
      } else {
	  rio_nprintf(rp_out, BLEN, "c Error at start of proof.  Unknown proof format '%s'\n", buf);
	  ok = false;
	  goto done;
      }
      if (is_binary) {
	  do {
	      rc = rio_readnb(rp_proof, &byte, 1);
	      if (rc == 0) {
		  rio_nprintf(rp_out, BLEN, "c No proof found\n");
		  ok = false;
		  goto done;
	      } else if (rc < 0) {
		  rio_nprintf(rp_out, BLEN, "c Error at start of proof: %s\n", err_buf);
		  ok = false;
		  goto done;
	      }
	  } while(byte == 0);
	  rio_unreadb(rp_proof);
      }
  }

  while (1) {
    if (!get_proof_clause(rp_proof, litList, is_binary, err_buf, BLEN)) {
	if (is_binary) 
	    rio_nprintf(rp_out, BLEN, "c Byte %zd.  ", rp_proof->byte_cnt);
	else
	    rio_nprintf(rp_out, BLEN, "c Line %zd.  ", rp_proof->line_cnt);
	rio_nprintf(rp_out, BLEN, "Couldn't read proof clause: %s\n", err_buf);
	ok = false;
	goto done;
    }
    int  *lits = litList->contents;
    int type = getType(lits);
    int cindex  = getIndex(lits);
    if (type == (int) 'd') {
      deleteClauses (lits + 2); }
    else if (type == (int) 'a') {
      int  index  = getIndex  (lits);
      lastIndex = index;
      int  length = getLength (lits);
      int* hints  = getHints  (lits);
      if (checkClause (lits + 2, length, hints) == SUCCESS) {
        addClause (cindex, lits + 2, length); 
	//	rio_nprintf(rp_out, BLEN, "c Checked and added clause #%d.  Length = %d (Bytes = %zd)\n", cindex, length, rp_proof->byte_cnt);
	if (length == 0)
	    goto done;
      }
      else {
	rio_nprintf(rp_out, BLEN, "c failed to check clause #%d: ", cindex); printClause (lits + 2);
	ok = false;
	goto done;
      }
    }
    else {
      if (is_binary) 
	  rio_nprintf(rp_out, BLEN, "c Byte %zd.  ", rp_proof->byte_cnt);
      else
	  rio_nprintf(rp_out, BLEN, "c Line %zd.  ", rp_proof->line_cnt);
      rio_nprintf(rp_out, BLEN, "Clause #%d.  Unknown type '%c' (0x%.2x)\n", 
		    cindex, type, type);
      ok = false;
      goto done;
    }
    index++;
  }
 done:
  if (ok)
      rio_nprintf(rp_out, BLEN, "c VERIFIED\n");
  else
      rio_nprintf(rp_out, BLEN, "c NOT VERIFIED\n");
  gettimeofday(&finish_time, NULL);
  double secs = (finish_time.tv_sec + 1e-6 * finish_time.tv_usec) -
      (start_time.tv_sec + 1e-6 * start_time.tv_usec);
  if (rp_proof)
      rio_nprintf(rp_out, BLEN, "c Proof bytes = %zd.\n", rp_proof->byte_cnt);
  else
      rio_nprintf(rp_out, BLEN, "c No proof bytes generated.\n");
  rio_nprintf(rp_out, BLEN, "c Added clauses = %lld.  Deleted clauses = %lld.  Max live clauses = %lld\n",
	 added_clauses, deleted_clauses, max_live_clauses);
  rio_nprintf(rp_out, BLEN, "c verification time = %.2f secs\n", secs);
  rio_flush(rp_out);
  int_list_free(litList);
  free(clsList);
  free(table);
  free(mask);
  free(intro);
  return ok;
}

