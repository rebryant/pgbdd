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

bool cnf_input = true;
bool text_input = true;
bool text_output = true;

int infd = STDIN_FILENO;
int outfd = STDOUT_FILENO;

/* Global data structures */
int_list_t *ilist = NULL;
rio_t rio_in, rio_out;

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
    if (first_time && cnf_input && text_output) {
	wc = rio_writenb(&rio_out, (uint8_t *) "p cnf ", 6);
	if (wc <= 0)
	    return false;
	/* Take away final 0 */
	ilist->count--;
	wc = rio_write_int_list_text(&rio_out, ilist, 1);
    } else if (cnf_input || !text_output ) {
	if (text_output) {
	    wc = rio_write_int_list_text(&rio_out, ilist, 0);
	}
	else
	    wc = rio_write_int_list_binary(&rio_out, ilist, 0);
    } else {
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
    }
    return wc > 1;
}

bool run_cnf_text() {
    char buf[12];
    int rc = 0;
    int val;
    size_t i;
    /* Skip initial comments */
    while (true) {
	rc = rio_read_token(&rio_in, (uint8_t *) buf, 12);
	if (rc <= 0) {
	    fprintf(stderr, "Line %zd.  Unexpected end of file\n", rio_in.line_cnt);
	    return false;
	}
	if (buf[0] == 'c') {
	    comment_count++;
	    rc = rio_skip_line(&rio_in);
	    if (rc < 0) {
		fprintf(stderr, "Line %zd.  Error reading comment\n", rio_in.line_cnt);
		return false;
	    }
	} else
	    break;
    }
    int_list_reset(ilist);

    if (buf[0] != 'p') {
	fprintf(stderr, "Line %zd.  Unknown line type '%c'\n", rio_in.line_cnt, buf[0]);
	return false;
    }
    int_list_append(ilist, buf[0]);
    /* Skip 'cnf' */
    rc = rio_read_token(&rio_in, (uint8_t *) buf, 12);
    if (rc <= 0) {
	fprintf(stderr, "Line %zd.  Unexpected end of file\n", rio_in.line_cnt);
	return false;
    }
    /* Get input parameters */
    for (i = 0; i < 2; i++) {
	rc = rio_read_token(&rio_in, (uint8_t *) buf, 12);
	if (rc <= 0) {
	    fprintf(stderr, "Line %zd.  Invalid header line\n", rio_in.line_cnt);
	    return false;
	}
	if (sscanf(buf, "%d", &val) != 1) {
	    fprintf(stderr, "Line %zd.  Invalid header line\n", rio_in.line_cnt);
	    return false;
	}
	int_list_append(ilist, val);
    }
    /* Put 0 at end */
    int_list_append(ilist, 0);
    if (!process_int_list(true)) {
	fprintf(stderr, "Input line %zd.  Output failed.  List length = %zd\n", rio_in.line_cnt, ilist->count);
	return false;
    }
    /* Get clauses */
    while (true) {
	/* Skip comments */
	while (true) {
	    rc = rio_read_token(&rio_in, (uint8_t *) buf, 12);
	    if (rc == 0)
		return true;
	    if (rc < 0) {
		fprintf(stderr, "Line %zd.  Error reading file\n", rio_in.line_cnt);
		return false;
	    }
	    if (buf[0] == 'c') {
		comment_count++;
		rc = rio_skip_line(&rio_in);
		if (rc == 0)
		    return true;
		if (rc < 0) {
		    fprintf(stderr, "Line %zd.  Error reading comment\n", rio_in.line_cnt);
		    return false;
		}
	    } else
		break;
	}
	int_list_reset(ilist);
	if (sscanf(buf, "%d", &val) != 1) {
	    fprintf(stderr, "Line %zd.  Invalid initial integer\n", rio_in.line_cnt);
	    return false;
	}
	int_list_append(ilist, val);
	if (val != 0) {
	    rc = rio_read_int_list_text(&rio_in, ilist);
	    if (rc < 0) {
		fprintf(stderr, "Line %zd.  Error reading file\n", rio_in.line_cnt);
		return false;
	    }
	}
	if (!process_int_list(false)) {
	    fprintf(stderr, "Input line %zd.  Output failed\n", rio_in.line_cnt);
	    return false;
	}
	clause_count++;
    }
    return true;
}

bool run_cnf_binary() {
    bool first_time = true;
    int rc;
    int cn = 0;
    do {
	int_list_reset(ilist);
	rc = rio_read_int_list_binary(&rio_in, ilist);
	if (rc < 0) {
	    fprintf(stderr, "Byte %zd.  Error reading file\n", rio_in.byte_cnt);
	    return false;
	}
	
	if (!process_int_list(first_time)) {
	    cn = ilist->count = 0 ? 0 : ilist->contents[0];
	    fprintf(stderr, "Failed on clause %d\n", cn);
	    return false;
	}
	if (!first_time)
	    clause_count++;
	first_time = false;
    } while (ilist->count > 1);
    return true;
}

bool run_proof_text() {
    char buf[12];
    int rc = 0;
    int val;
    size_t i;
    bool get_antecedents = false;
    /* Get clauses */
    while (true) {
	/* Skip comments */
	while (true) {
	    rc = rio_read_token(&rio_in, (uint8_t *) buf, 12);
	    if (rc == 0)
		return true;
	    if (rc < 0) {
		fprintf(stderr, "Line %zd.  Error reading file\n", rio_in.line_cnt);
		return false;
	    }
	    if (buf[0] == 'c') {
		comment_count++;
		rc = rio_skip_line(&rio_in);
		if (rc == 0)
		    return true;
		if (rc < 0) {
		    fprintf(stderr, "Line %zd.  Error reading comment\n", rio_in.line_cnt);
		    return false;
		}
	    } else
		break;
	}
	if (!get_antecedents)
	    int_list_reset(ilist);
	if (sscanf(buf, "%d", &val) != 1) {
	    fprintf(stderr, "Line %zd.  Invalid initial integer\n", rio_in.line_cnt);
	    return false;
	}
	int_list_append(ilist, val);
	if (get_antecedents) 
	    get_antecedents = false;
	else {
	    rc = rio_read_token(&rio_in, (uint8_t *) buf, 12);
	    if (rc <= 0) {
		fprintf(stderr, "Line %zd.  Error reading file\n", rio_in.line_cnt);
		return false;
	    }
	    if (buf[0] == 'd') {
		delete_count++;
		int_list_append(ilist, 'd');
		get_antecedents = false;
	    } else {
		int_list_append(ilist, 'a');
		get_antecedents = true;
		clause_count++;
		if (sscanf(buf, "%d", &val) != 1) {
		    fprintf(stderr, "Line %zd.  Invalid integer\n", rio_in.line_cnt);
		    return false;
		}
		int_list_append(ilist, val);
	    }
	}
	if (val != 0) {
	    rc = rio_read_int_list_text(&rio_in, ilist);
	    if (rc < 0) {
		fprintf(stderr, "Line %zd.  Error reading file\n", rio_in.line_cnt);
		return false;
	    }
	}
	if (!get_antecedents) {
	    if (!process_int_list(false)) {
		fprintf(stderr, "Input line %zd.  Output failed\n", rio_in.line_cnt);
		return false;
	    }
	}
    }
    return true;
}

bool run_proof_binary() {
    int rc;
    int last_cn = 0;
    int cn;
    while (true) {
	int_list_reset(ilist);
	rc = rio_read_int_list_binary(&rio_in, ilist);
	if (rc == 0)
	    return true;
	if (rc < 0) {
	    fprintf(stderr, "Byte %zd.  Error reading clause\n", rio_in.byte_cnt);
	    return false;
	}
	if (ilist->count >= 2 && ilist->contents[1] == 'a') {
	    clause_count++;
	    /* Get antecedents */
	    rc = rio_read_int_list_binary(&rio_in, ilist);
	    if (rc < 0) {
		fprintf(stderr, "Byte %zd.  Error reading antecedents\n", rio_in.byte_cnt);
		return false;
	    }
	} else {
	    delete_count++;
	}
	cn = ilist->count == 0 ? -1 : ilist->contents[0];
	if (!process_int_list(false)) {
	    fprintf(stderr, "Failed on clause %d (after clause %d)\n", cn, last_cn);
	    return false;
	}
	last_cn = cn;
    }
    return true;
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
    if (text_input) {
	if (cnf_input)
	    ok = run_cnf_text();
	else
	    ok = run_proof_text();
    } else {
	if (cnf_input)
	    ok = run_cnf_binary();
	else
	    ok = run_proof_binary();
    }
    if (have_infile) {
	close(infd);
    }
    rio_flush(&rio_out);
    if (have_outfile) {
	close(outfd);
    }

    fprintf(stderr, "Result:\n");
    if (text_input) {
	fprintf(stderr, "  Lines processed: %zd\n", rio_in.line_cnt);
	fprintf(stderr, "  Comment lines: %zd\n", comment_count);
    }
    fprintf(stderr, "  Input bytes: %zd\n", rio_in.byte_cnt);
    fprintf(stderr, "  Output bytes: %zd\n", rio_out.byte_cnt);    
    fprintf(stderr, "  Output clauses: %zd\n", clause_count);
    if (!cnf_input)
	fprintf(stderr, "  Output deletions: %zd\n", delete_count);

    return ok ? 0 : 1;
}
