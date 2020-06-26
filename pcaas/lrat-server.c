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
#include <sys/types.h>
#include <sys/wait.h>
#include <signal.h>
#include <stdarg.h>
#include <sys/time.h>
#include <time.h>

#include "stream.h"

#define MAXLINE 1024

/* Defined in lrat.c */
bool check_proof(rio_t *rp_cnf, rio_t *rp_proof, bool is_binary, rio_t *rp_out);

/* Default port: Year of George Boole's birth */
char *default_port = "1815";
rio_t rio_in;
rio_t rio_out;
int client_id = 0;

void usage(char *name) {
    fprintf(stdout, "Usage: %s [-h] [-d] [-P port] [-L logfile] [-v 0-4]\n", name);
    fprintf(stdout, "  -h         Print this message\n");
    fprintf(stdout, "  -d         Run as daemon\n");
    fprintf(stdout, "  -P port    Specify port number\n");
    fprintf(stdout, "  -L logfile Maintain log file\n");
    fprintf(stdout, "  -v vlevel  Set logging level (0-4)\n");
    exit(0);
}

typedef enum {LOG_NONE, LOG_ERROR, LOG_WARN, LOG_INFO, LOG_DEBUG } log_type_t;

const char *log_table[5] = {"NONE", "ERROR", "WARNING", "INFO", "DEBUG"};

bool have_log = false;
char logname[MAXLINE] = "";
int loglevel = LOG_INFO;
bool stdout_closed = false;

static void log_printf(log_type_t level, const char *format, ...) {
    struct timeval ltime;
    struct tm tinfo;
    char tbuf[MAXLINE] = "";
    if (level > loglevel)
	return;
    if (gettimeofday(&ltime, NULL) == 0) {
	localtime_r((time_t *) &(ltime.tv_sec), &tinfo);
	asctime_r(&tinfo, tbuf);
	size_t len = strlen(tbuf);
	if (len > 0 && tbuf[len-1] == '\n')
	    tbuf[len-1] = '\0';
    }
    va_list ap;
    if (!stdout_closed) {
	va_start(ap, format);
	if (strlen(tbuf) > 0)
	    fprintf(stdout, "%s %s:", tbuf, log_table[level]);
	else
	    fprintf(stdout, "%s:", log_table[level]);	  
	vfprintf(stdout, format, ap);
	fflush(stdout);
    }
    if (have_log) {
	FILE *lfile = fopen(logname, "a");
	if (lfile == NULL)
	    return;
	va_start(ap, format);
	if (strlen(tbuf) > 0)
	    fprintf(lfile, "%s %s:", tbuf, log_table[level]);
	else
	    fprintf(lfile, "%s:", log_table[level]);	  
	vfprintf(lfile, format, ap);
	fclose(lfile);
    }
}

void sigchld_handler(int sig) {
    while (waitpid(-1, 0, WNOHANG) > 0)
	;
    return;
}

void process_client(int connfd) {
    struct timeval start_time, finish_time;
    gettimeofday(&start_time, NULL);
    rio_initb(&rio_in, connfd);
    rio_initb(&rio_out, connfd);
    bool ok = check_proof(&rio_in, NULL, true, &rio_out);
    if (rio_flush(&rio_out) < 0)
	log_printf(LOG_WARN, "Client #%d.  Unable to complete flush. %zd bytes received. %zd bytes sent.\n",
		   client_id, rio_in.byte_cnt, rio_out.byte_cnt);
    gettimeofday(&finish_time, NULL);
    double secs = (finish_time.tv_sec + 1e-6 * finish_time.tv_usec) -
	(start_time.tv_sec + 1e-6 * start_time.tv_usec);
    if (ok)
	log_printf(LOG_INFO, "Client #%d. Proof completed. %zd bytes received. %zd bytes sent. %.1f seconds elapsed\n",
		   client_id, rio_in.byte_cnt, rio_out.byte_cnt, secs);
    else 
	log_printf(LOG_WARN, "Client #%d. Proof NOT completed. %zd bytes received. %zd bytes sent. %.1f seconds elapsed\n",
		   client_id, rio_in.byte_cnt, rio_out.byte_cnt, secs);
    close(connfd);
}

int main(int argc, char *argv[]) {
    int listenfd, connfd;
    socklen_t clientlen=sizeof(struct sockaddr_storage);
    struct sockaddr_storage clientaddr;
    char client_hostname[MAXLINE], client_port[MAXLINE];
    char port[MAXLINE] = "";
    bool run_daemon = false;
    int c;

    while ((c = getopt(argc, argv, "hdP:L:v:")) != -1) {
	switch(c) {
	case 'h':
	    usage(argv[0]);
	case 'd':
	    run_daemon = true;
	    break;
	case 'P':
	    strcpy(port, optarg);
	    break;
	case 'L':
	    strcpy(logname, optarg);
	    have_log = true;
	    break;
	case 'v':
	    loglevel = atoi(optarg);
	    break;
	default:
	    fprintf(stderr, "Unrecognized option -%c\n", c);
	    usage(argv[0]);
	}
    }
    if (strlen(port) == 0)
	strcpy(port, default_port);

    signal(SIGCHLD, sigchld_handler);
    listenfd = open_listenfd(port);
    if (listenfd < 0) {
	if (listenfd == -1 && errno == EADDRINUSE) {
	    log_printf(LOG_DEBUG, "Server already running on port %s\n", port);
	    return 0;
	}
	log_printf(LOG_ERROR, "Cannot set up listening socket on port %s\n", port);
	return 1;
    }
    log_printf(LOG_INFO, "Set up server on port %s\n", port);

    /* Run as standalone server */
    if (have_log) {
	close(STDOUT_FILENO);
	close(STDERR_FILENO);
	close(STDIN_FILENO);
	stdout_closed = true;
    }

    /* Run as daemon */
    if (run_daemon) {
	if (fork() != 0)
	    /* Parent exits while child keeps running */
	    exit(0);
    }    
    while (1) {
	connfd = accept(listenfd, (struct sockaddr *) &clientaddr, &clientlen);
	if (connfd < 0) {
	    log_printf(LOG_ERROR, "Accept returned %d\n", connfd);
	    exit(1);
	}
	client_id++;
	if (getnameinfo((struct sockaddr *) &clientaddr, clientlen, client_hostname, MAXLINE,
			client_port, MAXLINE, 0) == 0) {
	    log_printf(LOG_INFO, "Client #%d connected from %s:%s\n", client_id, client_hostname, client_port);
	} else
	    log_printf(LOG_INFO, "Client #%d connected\n", client_id);
	if (fork() == 0) {
	    close(listenfd);
	    process_client(connfd);
	    exit(0);
	} else
	    close(connfd);
    }
    return 0;
}
