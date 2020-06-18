/* Test of stream code */
/* Translate between different versions of integer lists */

#include <stdlib.h>
#include <stdbool.h>
#include <unistd.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>

#include "csapp-subset.h"
#include "stream.h"


static void usage(char *name) {
    fprintf(stderr, "Usage: %s [-h] [-I (t|b)] [-O (t|b)] [-i INFILE] [-o OUTFILE]\n", name);
    fprintf(stderr, "  -h           Print this message\n");
    fprintf(stderr, "  -I (t|b)     Specify input format as text or binary\n");
    fprintf(stderr, "  -O (t|b)     Specify output format as text or binary\n");
    fprintf(stderr, "  -i INFILE    Specify input file\n");
    fprintf(stderr, "  -o OUTFILE   Specify output file\n");
    exit(0);
}

bool text_input = true;
bool text_output = true;

int infd = STDIN_FILENO;
int outfd = STDOUT_FILENO;

/* Global data structures */
packet_buffer_t *text_inbuf = NULL;
packet_buffer_t *bin_inbuf = NULL;
packet_buffer_t *text_outbuf = NULL;
packet_buffer_t *bin_outbuf = NULL;
int_list_t *ilist = NULL;
rio_t rio;

/* Statistics gathering */
size_t list_count = 0;
size_t comment_count = 0;
size_t line_count = 0;
size_t int_count = 0;
size_t input_bytes = 0;
size_t output_bytes = 0;

static void init() {
    text_inbuf = packet_buffer_new(PACKET_STRING, 0);
    bin_inbuf = packet_buffer_new(PACKET_ILIST, 0);
    text_outbuf = packet_buffer_new(PACKET_STRING, 0);
    bin_outbuf = packet_buffer_new(PACKET_ILIST, 0);
    ilist = int_list_new(0);
    rio_readinitb(&rio, infd);
}


bool process_int_list(int_list_t *ilist) {
    if (ilist->count == 0)
	/* Empty line */
	return true;
    packet_buffer_t *outbuf = text_output ? text_outbuf : bin_outbuf;
    packet_buffer_reset(outbuf);
    if (!encode_int_list(outbuf, ilist))
	return false;
    int_count += ilist->count;
    list_count++;
    output_bytes += outbuf->plength;
    return payload_write(outfd, outbuf);
}

bool process_line(packet_buffer_t *pbuf) {
    if (pbuf->plength == 0)
	/* Empty */
	return true;
    /* Check for comment or p */
    if (pbuf->buffer->type == PACKET_STRING && 
	(pbuf->buffer->payload[0] == 'c' || pbuf->buffer->payload[0] == 'p')) {
	comment_count++;
	if (text_output)
	    /* Pass to output */
	    return payload_write(outfd, pbuf);
	else
	    return true;
    }
    int_list_reset(ilist);
    if (!decode_int_list(pbuf, ilist))
	return false;
    return process_int_list(ilist);
}

bool run_text() {
    int line = 0;
    while (true) {
	line++;
	packet_buffer_reset(text_inbuf);
	if (!packet_buffer_readlineb(&rio, text_inbuf)) {
	    fprintf(stderr, "Couldn't read line %d.  Aborting\n", line);
	    return false;
	}
	if (!process_line(text_inbuf)) {
	    fprintf(stderr, "Couldn't process line %d.  Aborting\n", line);
	    return false;
	}
	if (text_inbuf->plength == 0)
	    break;
	input_bytes += text_inbuf->plength;
	line_count++;
    }
    return true;
}

bool run_bin() {
    while (true) {
	int_list_reset(ilist);
	if (!int_list_read_binary(&rio, ilist)) {
	    fprintf(stderr, "Error reading binary file\n");
	    return false;
	}
	if (!process_int_list(ilist)) {
	    fprintf(stderr, "Couldn't process integer list\n");
	    return false;
	}
	if (ilist->count == 0)
	    break;
    }
    return true;
}

int main(int argc, char *argv[]) {
    int c;
    char infile[1024] = "";
    char outfile[1024] = "";
    bool have_infile = false;
    bool have_outfile = false;
    while ((c = getopt(argc, argv, "hi:o:I:O:")) != -1) {
	switch (c) {
	case 'h':
	    usage(argv[0]);
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
    bool ok = text_input ? run_text() : run_bin();
    if (have_infile) {
	close(infd);
    }
    if (have_outfile) {
	close(outfd);
    }

    fprintf(stderr, "Result:\n");
    if (text_input) {
	fprintf(stderr, "  Lines processed: %zd\n", line_count);
	fprintf(stderr, "  Comment lines: %zd\n", comment_count);
    }
    fprintf(stderr, "  Input bytes: %zd\n", input_bytes);
    fprintf(stderr, "  Integer lists: %zd\n", list_count);
    fprintf(stderr, "  Integers: %zd\n", int_count);
    fprintf(stderr, "  Output bytes: %zd\n", output_bytes);    

    return ok ? 0 : 1;
}
