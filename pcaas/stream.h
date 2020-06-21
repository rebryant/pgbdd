#ifndef __STREAM_H__
#define __STREAM_H__

/* Support for multiple proof file formats and for proof checking server */
#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <stdbool.h>
#include <unistd.h>
#include <errno.h>
#include <string.h>
#include <sys/types.h>
#include <sys/socket.h>
#include <netdb.h>

/****** Reliable I/O *******************************************************/

/*
 * The reliable I/O (rio) package provides reliable, buffered input and output
 * that works both with files and with Internet sockets.
 *
 * The code originated as part of material for the book:
 * R. E. Bryant and D. R. O'Hallaron, "Computer Systems: A Programmer's Perspective"
 * 3rd edition, 2016.
 *
 * Here, it has been extended to support buffered output, as well as input, 
 * and with features useful for SAT solvers and proof checkers.
 */

/* Persistent state for the robust I/O (Rio) package
 * This structure can be used for either buffered input, or for buffered output.
 * But, if a file descriptor is used for both reading and writing,
 * separate structures should be used
 */
#define RIO_BUFSIZE 8192
typedef struct {
    int rio_fd;                /* Descriptor for this internal buf */
    int rio_cnt;               /* Unread/unwritten bytes in internal buf */
    size_t line_cnt;              /* For keeping track of lines when reading text files */
    size_t byte_cnt;              /* For keeping track of byte position when reading binary files */
    uint8_t *rio_bufptr;          /* Next unread/writeable byte in internal buf */
    uint8_t rio_buf[RIO_BUFSIZE]; /* Internal buffer */
} rio_t;


/* Rio (Robust I/O) package API */

/* Initialization */
void rio_initb(rio_t *rp, int fd);

/* Buffered reading */
// ssize_t rio_readn(int fd, uint8_t *usrbuf, size_t n);

/*
 * Read (up to) n bytes.
 *  Return value -1 indicates error
 *  0 indicates EOF,
 *  < n indicates short read due to EOF
 */
ssize_t	rio_readnb(rio_t *rp, uint8_t *usrbuf, size_t n);

/* Find next space-delimited token.  Return number of characters in result */
/* Return value -1 indicates error, 0 indicates EOF */
int rio_read_token(rio_t *rp, uint8_t *usrbuf, size_t maxn);

/* Read through input until encounter next newline character */
int rio_skip_line(rio_t *rp);

/*
 * Write (up to) n bytes.
 *  Return value -1 indicates error
 *  < n indicates short read due to EOF
 */
ssize_t rio_writenb(rio_t *rp, uint8_t *usrbuf, size_t n);

/*
 * Write current contents of RIO buffer
 */
ssize_t rio_flush(rio_t *rp);

/****** Compressed integer (cint) support *******************************************/

/* Max bytes for byte representation of compressed integer */
#define CINT_LENGTH 5

int cint2int(uint8_t *bytes, int *value, int maxbytes);
int int2cint(uint8_t *bytes, int value);

/****** Integer list support **************************************************/

/* Data structure for representing dynamic, integer lists */
typedef struct {
    size_t count; /* Number of integers in list */
    size_t alloc_size; /* Number of byte allocated for entire buffer */
    int *contents;
} int_list_t;

/* Generate new list.  give hint about possible length */
int_list_t *int_list_new(size_t possible_length);

/* Reset list to be empty */
void int_list_reset(int_list_t *ilist);

/* Free list */
void int_list_free(int_list_t *ilist);

/* Append integer to list */
bool int_list_append(int_list_t *ilist, int value);

/* Write text representation of integer list */
ssize_t rio_write_int_list_text(rio_t *rp, int_list_t *ilist, size_t start_index);

/* Write compressed binary representation of integer list */
ssize_t rio_write_int_list_binary(rio_t *rp, int_list_t *ilist, size_t start_index);

/* 
 * Read text representation of integer list.
 * Stop when encounter 0
 * Append to existing list
 */
ssize_t rio_read_int_list_text(rio_t *rp, int_list_t *ilist);

/* 
 * Read compressed binary representation of integer list.
 * Stop when encounter compressed representation of 0
 * Append to existing list
 */
ssize_t rio_read_int_list_binary(rio_t *rp, int_list_t *ilist);


/****** Client/server support *************************************************/

/* Reentrant protocol-independent client/server helpers */

/* Misc constants */
#define LISTENQ  1024  /* Second argument to listen() */

int open_clientfd(char *hostname, char *port);
int open_listenfd(char *port);

#endif /* __STREAM_H__ */
