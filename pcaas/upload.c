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

/* Upload a CNF/LRATB combination to proof server */

#include <stdio.h>
#include <stdlib.h>
#include <fcntl.h>

#include "stream.h"

#define BSIZE RIO_BUFSIZE
#define BLEN  256

char *default_port = "1815";
char *default_host = "localhost";

rio_t rio_upload;
rio_t rio_download;
rio_t rio_out;

/* Exit function */
void flusher() {
    rio_flush(&rio_out);
}


void usage(char *name) {
    rio_nprintf(&rio_out, BLEN, "Usage: %s [-h] [-m (b|t)] [-H host] [-P port] -c file1.cnf [-l file2.lrat[b]]\n", name);
    rio_nprintf(&rio_out, BLEN, "  -h               Print this message\n");
    rio_nprintf(&rio_out, BLEN, "  -m (b|t)         Accept proof file from standard input in either binary (b) or text(t) format\n");
    rio_nprintf(&rio_out, BLEN, "  -H host          Specify server host\n");
    rio_nprintf(&rio_out, BLEN, "  -P port          Specify server port\n");
    rio_nprintf(&rio_out, BLEN, "  -c file1.cnf     Specify CNF file\n");    
    rio_nprintf(&rio_out, BLEN, "  -l file2.lrat[b] Specify proof file in either text (.lrat) or binary (.lratb) fomrat\n");    
    exit(0);
}

bool upload_stdin() {
    uint8_t buf[BSIZE];
    rio_t rio_in;
    ssize_t nread = 0;
    ssize_t rc = 0;
    ssize_t wc = 0;

    rio_initb(&rio_in, STDIN_FILENO);
    while ((rc = rio_readnb(&rio_in, buf, BSIZE)) > 0) {
	nread += rc;
	wc = rio_writenb(&rio_upload, buf, rc);
	if (wc != rc) {
	    rio_nprintf(&rio_out, BLEN, "Error sending standard input to server.  %zd bytes read\n", nread);
	    return false;
	}
    }

    if (rc < 0) {
	rio_nprintf(&rio_out, BLEN, "Error reading standard input.  %zd bytes read\n", nread);
	return false;
    }
    return true;
}

bool upload_file(char *fname) {
    uint8_t buf[BSIZE];
    rio_t rio_in;
    int fd = open(fname, O_RDONLY);
    ssize_t nread = 0;
    ssize_t rc = 0;
    ssize_t wc = 0;

    if (fd < 0) {
	rio_nprintf(&rio_out, BLEN, "Couldn't open input file '%s'\n", fname);
	return false;
    }
    rio_initb(&rio_in, fd);
    while ((rc = rio_readnb(&rio_in, buf, BSIZE)) > 0) {
	nread += rc;
	wc = rio_writenb(&rio_upload, buf, rc);
	if (wc != rc) {
	    rio_nprintf(&rio_out, BLEN, "Error writing file '%s' to server.  %zd bytes read\n", fname, nread);
	    return false;
	}
    }

    if (rc < 0) {
	rio_nprintf(&rio_out, BLEN, "Error reading file '%s'.  %zd bytes read\n", fname, nread);
	return false;
    }
    close(fd);
    return true;
}

bool upload_text(char *text) {
    size_t len = strlen(text);
    if (rio_writenb(&rio_upload, (uint8_t *) text, len) != len) {
	rio_nprintf(&rio_out, BLEN, "Error writing text '%s' to server\n", text);
	return false;
    }
    return true;
}

bool upload_null() {
    uint8_t byte = 0;
    if (rio_writenb(&rio_upload, &byte, 1) != 1) {
	rio_nprintf(&rio_out, BLEN, "Error writing null byte to server\n");
	return false;
    }
    return true;
}

#define NSIZE 64

int main(int argc, char *argv[]) {
    char cnf_name[NSIZE] = "";
    char lrat_name[NSIZE] = "";
    char host[NSIZE] = "";
    char port[NSIZE] = "";
    uint8_t buf[BSIZE];
    int rc, c;
    bool is_binary = false;
    bool use_stdin = false;
    rio_initb(&rio_out, STDOUT_FILENO);
    atexit(flusher);
    while ((c = getopt(argc, argv, "hm:H:P:c:l:")) != -1) {
	switch(c) {
	case 'h':
	    usage(argv[0]);
	case 'm':
	    use_stdin = true;
	    if (optarg[0] == 'b')
		is_binary = true;
	    else if (optarg[0] != 't') {
		rio_nprintf(&rio_out, BLEN, "Unknown input mode '%s'\n", optarg);
		usage(argv[0]);
	    }
	    break;
	case 'c':
	    strcpy(cnf_name, optarg);
	    break;
	case 'l':
	    strcpy(lrat_name, optarg);
	    is_binary = optarg[strlen(optarg)-1] == 'b';
	    break;
	case 'H':
	    strcpy(host, optarg);
	    break;
	case 'P':
	    strcpy(port, optarg);
	    break;
	default:
	    rio_nprintf(&rio_out, BLEN, "Unknown option -%c\n", c);
	    usage(argv[0]);
	}
    }
    if (strlen(cnf_name) == 0) {
	rio_nprintf(&rio_out, BLEN, "Require CNF file\n");
	usage(argv[0]);
    }
    if (strlen(lrat_name) == 0 && !use_stdin) {
	rio_nprintf(&rio_out, BLEN, "Require either LRAT[B] file or pipe mode specification\n");
	usage(argv[0]);
    }
    if (strlen(host) == 0)
	strcpy(host, default_host);
    if (strlen(port) == 0)
	strcpy(port, default_port);
    int client_fd = open_clientfd(host, port);
    if (client_fd > 0) {
	rio_nprintf(&rio_out, BLEN, "Opened connection to %s:%s\n", host, port);
    } else {
	rio_nprintf(&rio_out, BLEN, "Couldn't establish connection to %s:%s\n", host, port);
	exit(1);
    }
    rio_initb(&rio_upload, client_fd);
    rio_initb(&rio_download, client_fd);
    if (!upload_file(cnf_name))
	return 1;
    if (is_binary) {
	if (!upload_text(" DONE BINARY "))
	    return 1;
	if (!upload_null())
	    return 1;
    } else {
	if (!upload_text(" DONE TEXT "))
	    return 1;
    }

    if (use_stdin) {
	if (!upload_stdin())
	    return 1;
    } else {
	if (!upload_file(lrat_name))
	    return 1;
    }

    if (rio_flush(&rio_upload) < 0)
	return 1;;
    
    /* Get response from server */
    while ((rc = rio_readnb(&rio_download, buf, BSIZE)) > 0) {
	rio_writenb(&rio_out, buf, rc);
    }
    if (rc < 0) {
	rio_nprintf(&rio_out, BLEN, "Error downloading response\n");
    }
    rio_nprintf(&rio_out, BLEN, "Uploaded %zd bytes.  Received %zd bytes in response\n", 
		rio_upload.byte_cnt, rio_download.byte_cnt);
    return 0;
}
