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

/* Support for Proof server */
#include <stdio.h>
#include <stdlib.h>
#include <signal.h>
#include <stdarg.h>

#include "stream.h"

/* Defined in lrat.c */
bool check_proof(rio_t *rp_cnf, rio_t *rp_proof, bool is_binary, rio_t *rp_out);


/* Default port: Year of George Boole's birth */
char *port = "1815";
rio_t rio_in;
rio_t rio_out;

typedef enum {LOG_ERROR, LOG_WARN, LOG_INFO, LOG_DEBUG } log_type_t;

const char *log_table[4] = {"ERROR", "WARNING", "INFO", "DEBUG"};


static void log_printf(log_type_t level, const char *format, ...) {
    va_list ap;
    va_start(ap, format);
    int rval = 0;
    if (level <= LOG_DEBUG) {
	rval += fprintf(stdout, "%s:", log_table[level]);
	rval += vfprintf(stdout, format, ap);
	fflush(stdout);
    }
}

void sigchld_handler(int sig) {
    while (waitpid(-1, 0, WNOHANG) > 0)
	;
    return;
}

int main(int argc, char *argv[]) {
    int listenfd, connfd;
    socklen_t clientlen=sizeof(struct sockaddr_in);
    struct sockaddr_in clientaddr;

    if (argc > 1)
	port = argv[1];

    signal(SIGCHLD, sigchld_handler);
    listenfd = open_listenfd(port);
    if (listenfd < 0) {
	log_printf(LOG_ERROR, "Cannot set up listening socket on port %s\n", port);
	return 1;
    }
    log_printf(LOG_DEBUG, "Set up server on port %s\n", port);
    while (1) {
	connfd = accept(listenfd, (struct sockaddr *) &clientaddr, &clientlen);
	log_printf(LOG_DEBUG, "New client connected\n");
	if (fork() == 0) {
	    close(listenfd);
	    rio_initb(&rio_in, connfd);
	    rio_initb(&rio_out, STDOUT_FILENO);
	    if (check_proof(&rio_in, &rio_in, true, &rio_out))
		log_printf(LOG_INFO, "Proof completed\n");
	    else
		log_printf(LOG_WARN, "Could not complete proof\n");
	}
	close(connfd);
    }
}
