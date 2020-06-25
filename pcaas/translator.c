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

/* Test of stream code */
/* Translate between different versions of proofs and CNF files.
   All convert to integer list format, and so text-to-text and binary-to-binary
   provide useful checks of code.
 */

#include <stdlib.h>
#include <stdbool.h>
#include <unistd.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>

#include "stream.h"


static void usage(char *name) {
    fprintf(stderr, "Usage: %s [-h] -m (c|p) [-I (t|b)] [-O (t|b)] [-i INFILE] [-o OUTFILE]\n", name);
    fprintf(stderr, "  -h           Print this message\n");
    fprintf(stderr, "  -m (c|p)     Specify input file as CNF (c) or proof (p)\n");
    fprintf(stderr, "  -I (t|b)     Specify input format as text or binary\n");
    fprintf(stderr, "  -O (t|b)     Specify output format as text or binary\n");
    fprintf(stderr, "  -i INFILE    Specify input file\n");
    fprintf(stderr, "  -o OUTFILE   Specify output file\n");
    exit(0);
}

bool cnf_input = false;
bool text_input = true;
bool text_output = true;

int infd = STDIN_FILENO;
int outfd = STDOUT_FILENO;

/* Global data structures */
int_list_t *ilist = NULL;
rio_t rio_in, rio_out;

#define BLEN 1024
char err_buf[BLEN];

/* Statistics gathering */
size_t comment_count = 0;
size_t clause_count = 0;
size_t delete_count = 0;

static void init() {
    ilist = int_list_new(0);
    rio_initb(&rio_in, infd);
    rio_initb(&rio_out, outfd);
}


bool process_int_list(bool first_time) {
    ssize_t wc = 0;
    if (ilist->count == 0)
	/* Empty line */
	return true;
    if (cnf_input) {
	if (first_time) {
	    wc = rio_writenb(&rio_out, (uint8_t *) "p cnf ", 6);
	    if (wc <= 0)
	    return false;
	}
	wc = rio_write_int_list_text(&rio_out, ilist, 0);
    } else {
	if (text_output) {
	    /* Text representation of proof.  Must adjust line type */
	    int cn, c;
	    char buf[16];
	    int len = 0;
	    if (ilist->count < 3) {
		fprintf(stderr, "Can't have proof with only %zd tokens\n", ilist->count);
		return false;
	    }
	    cn = ilist->contents[0];
	    c = ilist->contents[1];
	    if (c == 'a') {
		len = sprintf(buf, "%d ",cn);
	    } else {
		len = sprintf(buf, "%d %c ", cn, c);
	    }
	    wc = rio_writenb(&rio_out, (uint8_t *) buf, len);
	    if (wc < 0)
		return false;
	    wc += rio_write_int_list_text(&rio_out, ilist, 2);
	} else
	    wc = rio_write_int_list_binary(&rio_out, ilist, 0);
    }
    return wc > 1;
}

bool run_cnf() {
    if (!get_cnf_header(&rio_in, ilist, err_buf, BLEN)) {
	fprintf(stderr, "%s\n", err_buf);
	return false;
    }
    if (!process_int_list(true)) {
	fprintf(stderr, "Input line %zd.  Output failed.\n", rio_in.line_cnt);
	return false;
    }
    /* Get clauses */
    while (true) {
	if (!get_cnf_clause(&rio_in, ilist, err_buf, BLEN)) {
	    fprintf(stderr, "%s\n", err_buf);
	    return false;
	}
	if (ilist->count == 0)
	    break;
	if (!process_int_list(false)) {
	    fprintf(stderr, "Input line %zd.  Output failed\n", rio_in.line_cnt);
	    return false;
	}
	clause_count++;
    }
    return true;
}

bool run_proof(bool is_binary) {
    /* Get clauses */
    while (true) {
	if (!get_proof_clause(&rio_in, ilist, is_binary, err_buf, BLEN)) {
	    fprintf(stderr, "%s\n", err_buf);
	    return false;
	}
	if (ilist->count == 0)
	    return true;
	if (!process_int_list(false)) {
	    fprintf(stderr, "Input line %zd.  Output failed\n", rio_in.line_cnt);
	    return false;
	}
	if (ilist->contents[1] == 'a')
	    clause_count++;
	else
	    delete_count++;
			  
    }
    fprintf(stderr, "Proof ended prematurely");
    return false;
}


int main(int argc, char *argv[]) {
    int c;
    char infile[1024] = "";
    char outfile[1024] = "";
    bool have_infile = false;
    bool have_outfile = false;
    while ((c = getopt(argc, argv, "hm:i:o:I:O:")) != -1) {
	switch (c) {
	case 'h':
	    usage(argv[0]);
	case 'm':
	    if (optarg[0] == 'c')
		cnf_input = true;
	    else if (optarg[0] == 'p')
		cnf_input = false;
	    else {
		fprintf(stderr, "Unknown content type '%c'\n", optarg[0]);
		usage(argv[0]);
	    }
	    break;
	case 'I':
	    if (optarg[0] == 't')
		text_input = true;
	    else if (optarg[0] == 'b')
		text_input = false;
	    else {
		fprintf(stderr, "Unknown file type '%c'\n", optarg[0]);
		usage(argv[0]);
	    }
	    break;
	case 'O':
	    if (optarg[0] == 't')
		text_output = true;
	    else if (optarg[0] == 'b')
		text_output = false;
	    else {
		fprintf(stderr, "Unknown file type '%c'\n", optarg[0]);
		usage(argv[0]);
	    }
	    break;
	case 'i':
	    strcpy(infile, optarg);
	    have_infile = true;
	    break;
	case 'o':
	    strcpy(outfile, optarg);
	    have_outfile = true;
	    break;
	default:
	    fprintf(stderr, "Unknown option '%c'\n", c);
	    usage(argv[0]);
	}
    }
    if (have_infile) {
	infd = open(infile, O_RDONLY);
	if (infd < 0) {
	    fprintf(stderr, "Couldn't open input file '%s'\n", infile);
	    exit(1);
	}
    }
    if (have_outfile) {
	outfd = open(outfile, O_WRONLY|O_CREAT|O_TRUNC, S_IRWXU);
	if (outfd < 0) {
	    fprintf(stderr, "Couldn't open output file '%s'\n", infile);
	    exit(1);
	}
    }
    init();
    bool ok;
    if (cnf_input) {
	if (!text_input || !text_output) {
	    fprintf(stderr, "CNF only has text form\n");
	    exit(1);
	}
	ok = run_cnf();
	
    } else {
	ok = run_proof(!text_input);
    }
    if (have_infile) {
	close(infd);
    }
    rio_flush(&rio_out);
    if (have_outfile) {
	close(outfd);
    }

    fprintf(stderr, "Result:\n");
    fprintf(stderr, "  Input bytes: %zd\n", rio_in.byte_cnt);
    fprintf(stderr, "  Output bytes: %zd\n", rio_out.byte_cnt);    
    fprintf(stderr, "  Output clauses: %zd\n", clause_count);
    if (!cnf_input)
	fprintf(stderr, "  Output deletions: %zd\n", delete_count);

    return ok ? 0 : 1;
}
