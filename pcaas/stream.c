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

#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <ctype.h>

#include "stream.h"



/****************************************
 * The Rio package - Robust I/O functions
 ****************************************/

/*
 * rio_initb - Associate a descriptor with a read or write buffer and reset buffer
 */
void rio_initb(rio_t *rp, int fd) 
{
    rp->rio_fd = fd;  
    rp->rio_cnt = 0;  
    rp->line_cnt = 0;
    rp->byte_cnt = 0;
    rp->rio_bufptr = rp->rio_buf;
}

/* 
 * rio_read - This is a wrapper for the Unix read() function that
 *    transfers min(n, rio_cnt) bytes from an internal buffer to a user
 *    buffer, where n is the number of bytes requested by the user and
 *    rio_cnt is the number of unread bytes in the internal buffer. On
 *    entry, rio_read() refills the internal buffer via a call to
 *    read() if the internal buffer is empty.
 */
static ssize_t rio_read(rio_t *rp, uint8_t *usrbuf, size_t n)
{
    int cnt;
    int i;
    while (rp->rio_cnt <= 0) {  /* Refill if buf is empty */
	rp->rio_cnt = read(rp->rio_fd, rp->rio_buf, sizeof(rp->rio_buf));
	if (rp->rio_cnt < 0) {
	    if (errno != EINTR) /* Interrupted by sig handler return */
		return -1;
	}
	else if (rp->rio_cnt == 0)  /* EOF */
	    return 0;
	rp->rio_bufptr = rp->rio_buf; /* Reset buffer ptr */
    }

    /* Copy min(n, rp->rio_cnt) bytes from internal buf to user buf */
    cnt = n;          
    if (rp->rio_cnt < n)   
	cnt = rp->rio_cnt;
    memcpy(usrbuf, rp->rio_bufptr, cnt);
    /* Check to see if any newlines were encountered */
    for (i = 0; i < cnt; i++)
	if (usrbuf[i] == (uint8_t) '\n')
	    rp->line_cnt++;
    rp->byte_cnt += cnt;
    rp->rio_bufptr += cnt;
    rp->rio_cnt -= cnt;
    return cnt;
}

/*
 * rio_readnb - Robustly read n bytes (buffered)
 */
ssize_t rio_readnb(rio_t *rp, uint8_t *usrbuf, size_t n) 
{
    size_t nleft = n;
    ssize_t nread;
    uint8_t *bufp = usrbuf;
    
    while (nleft > 0) {
	if ((nread = rio_read(rp, bufp, nleft)) < 0) 
            return -1;          /* errno set by read() */ 
	else if (nread == 0)
	    break;              /* EOF */
	nleft -= nread;
	bufp += nread;
    }
    return (n - nleft);         /* return >= 0 */
}

/* Find next space-delimited token.  Return number of characters in result */
/* Return value -1 indicates error, 0 indicates EOF */
/* *sep set to terminating separator */
int rio_read_token(rio_t *rp, uint8_t *usrbuf, size_t maxn, uint8_t *sep) {
    uint8_t byte;
    ssize_t rc = 0;
    int nread = 0;
    /* Skip any white space */
    do
	rc = rio_readnb(rp, &byte, 1);
    while (rc > 0 && isspace((char) byte));

    /* Read characters */
    while (rc > 0 && !isspace((char) byte) && byte != 0) {
	usrbuf[nread++] = byte;
	rc = rio_readnb(rp, &byte, 1);
    }
    /*
      When have combined CNF and proof, CNF ends with text "DONE"
      Proof begins with either "TEXT" or "BINARY"

      When text, have whitespace followed by proof in text format
      When binary, have one or more 0 bytes, followed by proof in binary format
    */
    /* Unget the terminating character so that it will be read again */
    if (byte == 0) {
	rio_unreadb(rp);
    }
    if (sep)
	*sep = byte;
    /* Terminate string */
    usrbuf[nread] = 0;
    return nread;
}

/* Read through input until encounter next newline character */
/* Return number of characters skipped */
int rio_skip_line(rio_t *rp) {
    uint8_t byte;
    int nread = 0;
    ssize_t rc = 0;
    do {
	rc = rio_readnb(rp, &byte, 1);
	nread += rc;
    } while (rc > 0 && (char) byte != '\n');
    return nread;
}

/*
 * Reset buffer by one character, effectively "unreading" it
 * Reliable if most recent read had rc > 0,
 * and can only be used once.
 */
void rio_unreadb(rio_t *rp) {
    rp->rio_cnt++;
    rp->rio_bufptr--;
    rp->byte_cnt--;
    if (*rp->rio_bufptr == (uint8_t) '\n')
	rp->line_cnt--;
}

/*
 * rio_writen - Robustly write n bytes (unbuffered)
 */
static ssize_t rio_writen(int fd, uint8_t *usrbuf, size_t n) 
{
    size_t nleft = n;
    ssize_t nwritten;
    uint8_t *bufp = usrbuf;

    while (nleft > 0) {
	if ((nwritten = write(fd, bufp, nleft)) <= 0) {
	    if (errno == EINTR)  /* Interrupted by sig handler return */
		nwritten = 0;    /* and call write() again */
	    else
		return -1;       /* errno set by write() */
	}
	nleft -= nwritten;
	bufp += nwritten;
    }
    return n;
}

/*
 * Write current contents of RIO buffer.  Return number of bytes flushed.
 */
ssize_t rio_flush(rio_t *rp) {
    ssize_t rval = rio_writen(rp->rio_fd, rp->rio_buf, rp->rio_cnt);
    rp->rio_cnt = 0;
    rp->rio_bufptr = rp->rio_buf;
    
    return rval;
}

/*
 * Write (up to) n bytes.
 *  Return value -1 indicates error
 *  < n indicates short read due to EOF
 */
ssize_t rio_writenb(rio_t *rp, uint8_t *usrbuf, size_t n) {
    ssize_t nflushed = 0;
    ssize_t nwritten = 0;
    if (n <= sizeof(rp->rio_buf)) {
	if (rp->rio_cnt + n > sizeof(rp->rio_buf)) {
	    nflushed = rio_flush(rp);
	    if (nflushed < 0)
		return nflushed;
	}
	memcpy(rp->rio_bufptr, usrbuf, n);
	rp->byte_cnt += n;
	rp->rio_cnt += n;
	rp->rio_bufptr += n;
	return n;
    } else {
	nflushed = rio_flush(rp);
	if (nflushed < 0)
	    return nflushed;
	nwritten = rio_writen(rp->rio_fd, usrbuf, n);
	rp->byte_cnt += nwritten;
	return nwritten;
    }
}    

/*
 * Like snprintf, except that writes to rio
 */
int rio_nprintf(rio_t *rp, size_t maxlen, const char *format, ...) {
    va_list ap;
    char buf[maxlen];
    va_start(ap, format);
    int count = vsnprintf(buf, maxlen, format, ap);
    return (int) rio_writenb(rp, (uint8_t *) buf, count);
}


/****** Compressed integer (cint) support *******************************************/

/* Read byte sequence to get integer value */
/* Return number of bytes read, or -1 if invalid */
int cint2int(uint8_t *bytes, int *value, int maxbytes) {
    unsigned int uval = 0;
    int count = 0;
    bool done = false;
    while (!done && count < maxbytes) {
	uint8_t nbyte = bytes[count++];
	uint8_t bval = (nbyte) & 0x7F;
	uint8_t hval = (bval>>7) & 0x1;
	if (((uval << 7) >> 7) != uval)
	    /* Value would overflow */
	    return -1;
	uval = (uval << 7) + bval;
	done = (hval != 1);
    }
    if (!done)
	return -1;
    int sign = uval & 0x1;
    int mag = (uval >> 1);
    *value = sign ? -mag : mag;
    return count;
}

/* Convert integer to byte representation */
/* Array bytes must be of length >= CINT_LENGTH */
/* Return length of encoded value */
int int2cint(uint8_t *bytes, int value) {
    unsigned int uval = value < 0 ? 2*(-value)+1 : 2*value;
    int count = 0;
    uint8_t nbyte = uval & 0x7F;
    uval = uval >> 7;
    while (uval) {
	bytes[count++] = (1 << 7) + nbyte;
	nbyte = uval & 0x7F;	
	uval = uval >> 7;
    }
    bytes[count++] = nbyte;
    return count;
}
/****** Integer list support **************************************************/

/* Minimum allocation */
#define MIN_ALLOC 16
/* How much should each allocation increase the overall amount */
#define REALLOC_RATIO 1.5

static bool int_list_check_size(int_list_t *ilist, size_t add) {
    size_t current = ilist->count * sizeof(int);
    size_t need = current + add * sizeof(int);
    if (need > ilist->alloc_size) {
	size_t min_size = (size_t) (REALLOC_RATIO * current);
	if (need < min_size) {
	    need = min_size;
	    /* Round up to multiple of int size */
	    need = ((need+sizeof(int)-1) / sizeof(int)) * sizeof(int);
	}
	ilist->contents = realloc(ilist->contents, need);
	if (ilist->contents == NULL)
	    return false;
	ilist->alloc_size = need;
    }
    return true;
}

/********** Exported functions for working with integer lists ********/

/* Generate new list.  give hint about possible length */
int_list_t *int_list_new(size_t possible_length) {
    int_list_t *ilist = malloc(sizeof(int_list_t));
    if (ilist == NULL)
	return NULL;
    ilist->alloc_size = possible_length * sizeof(int);
    if (ilist->alloc_size < MIN_ALLOC)
	ilist->alloc_size = MIN_ALLOC;
    ilist->contents = malloc(ilist->alloc_size);
    if (ilist->contents == NULL) {
	free(ilist);
	return NULL;
    }
    ilist->count = 0;
    return ilist;
}

/* Reset list to be empty */
void int_list_reset(int_list_t *ilist) {
    ilist->count = 0;
}

/* Free list */
void int_list_free(int_list_t *ilist) {
    if (!ilist)
	return;
    free(ilist->contents);
    free(ilist);
}

/* Append integer to list */
bool int_list_append(int_list_t *ilist, int value) {
    if (!int_list_check_size(ilist, 1))
	return false;
    ilist->contents[ilist->count++] = value;
    return true;
}

/* Write text representation of integer list */
ssize_t rio_write_int_list_text(rio_t *rp, int_list_t *ilist, size_t start_index) {
    char buf[12];
    ssize_t nwritten = 0;
    ssize_t nw = 0;
    size_t i;
    if (ilist->count <= start_index)
	return 0;
    nwritten = rio_nprintf(rp, 11, "%d", ilist->contents[start_index]);
    if (nwritten < 0)
	return nwritten;
    for (i = start_index + 1; i < ilist->count; i++) {
	nw = rio_nprintf(rp, 11, " %d", ilist->contents[i]);
	if (nw < 0)
	    return nw;
	nwritten += nw;
    }
    buf[0] = '\n';
    nw = rio_writenb(rp, (uint8_t *) buf, 1);
    if (nw < 0)
	return nw;
    nwritten += nw;
    return nwritten;
}

/* Write compressed binary representation of integer list */
ssize_t rio_write_int_list_binary(rio_t *rp, int_list_t *ilist, size_t start_index) {
    uint8_t buf[CINT_LENGTH];
    ssize_t nwritten = 0;
    ssize_t nw = 0;
    int len;
    size_t i;
    for (i = start_index; i < ilist->count; i++) {
	len = int2cint(buf, ilist->contents[i]);
	nw = rio_writenb(rp, (uint8_t *) buf, len);
	if (nw < 0)
	    return nw;
	nwritten += nw;
    }
    return nwritten;
}

/* Read byte sequence to get integer value */
/* Return number of bytes read (0 if EOF), or -1 if invalid */
static ssize_t rio_read_int_binary(rio_t *rp, int *value) {
    unsigned int uval = 0;
    bool done = false;
    unsigned weight = 0;
    int rc = 0;
    int count = 0;

    while (!done) {
	uint8_t nbyte;
	if ((rc = rio_readnb(rp, (void *) &nbyte, 1)) !=1)
	    break;
	count++;
	uint8_t bval = (nbyte) & 0x7F;
	uint8_t hval = (nbyte>>7) & 0x1;
	if (weight >= 8*sizeof(int) || ((bval << weight) >> weight) != bval)
	    /* Value would overflow */
	    return -1;
	uval += bval << weight;
	weight += 7;
	done = (hval != 1);
    }

    if (done) {
	int sign = uval & 0x1;
	int mag = (uval >> 1);
	*value = sign ? -mag : mag;
    }
    return rc;
}

/* 
 * Read text representation of integer list.
 * Stop when encounter 0
 * Append to existing list
 */
ssize_t rio_read_int_list_text(rio_t *rp, int_list_t *ilist) {
    char buf[10];
    ssize_t nread = 0;
    int rc = 0;
    int value;
    do {
	rc = rio_read_token(rp, (uint8_t *) buf, 10, NULL);
	if (rc <= 0)
	    break;
	if (sscanf(buf, "%d", &value) != 1)
	    return -1;
	nread += rc;
	int_list_append(ilist, value);
    } while (value != 0);
    if (rc < 0)
	return rc;
    return nread;
}

/* 
 * Read compressed binary representation of integer list.
 * Stop when encounter compressed representation of 0
 * Append to existing list
 */
ssize_t rio_read_int_list_binary(rio_t *rp, int_list_t *ilist) {
    ssize_t nread = 0;
    int rc = 0;
    int value;
    do {
	rc = rio_read_int_binary(rp, &value);
	if (rc <= 0)
	    break;
	nread += rc;
	int_list_append(ilist, value);
    } while (value != 0);
    if (rc < 0)
	return rc;
    return nread;
}


/******************************** 
 * Support for CNF and proofs
 ********************************/

/* Text to indicate CNF completed */
const char *done_text = "DONE";
const char *text_text = "TEXT";
const char *binary_text = "BINARY";

/* 
 * Read representation of header in CNF file.
 * Result stored in integer list with count 2 (number of variables, number of clauses)
 * Return value = true if successful
 * If error occurs, a diagnostic message is written to err_buf (up to maxlen characters)
 */
bool get_cnf_header(rio_t *rp, int_list_t *ilist, char *err_buf, size_t maxlen) {
    char buf[12];
    int rc = 0;
    int val;
    size_t i;
    uint8_t sep;
    /* Skip initial comments */
    while (true) {
	rc = rio_read_token(rp, (uint8_t *) buf, 12, &sep);
	if (rc <= 0) {
	    snprintf(err_buf, maxlen, "Line %zd.  Unexpected end of file", rp->line_cnt);
	    return false;
	}
	if (buf[0] == 'c') {
	    if (sep != '\n') {
		rc = rio_skip_line(rp);
		if (rc < 0) {
		    snprintf(err_buf, maxlen, "Line %zd.  Error reading comment", rp->line_cnt);
		    return false;
		}
	    }
	} else
	    break;
    }
    int_list_reset(ilist);
    if (buf[0] != 'p') {
	snprintf(err_buf, maxlen, "Line %zd.  Unknown line type '%s'", rp->line_cnt, buf);
	return false;
    }
    /* Skip 'cnf' */
    rc = rio_read_token(rp, (uint8_t *) buf, 12, NULL);
    if (rc <= 0) {
	snprintf(err_buf, maxlen, "Line %zd.  Unexpected end of file", rp->line_cnt);
	return false;
    }
    /* Get input parameters */
    for (i = 0; i < 2; i++) {
	rc = rio_read_token(rp, (uint8_t *) buf, 12, NULL);
	if (rc <= 0) {
	    snprintf(err_buf, maxlen, "Line %zd.  Invalid header line", rp->line_cnt);
	    return false;
	}
	if (sscanf(buf, "%d", &val) != 1) {
	    snprintf(err_buf, maxlen, "Line %zd.  Invalid header line", rp->line_cnt);
	    return false;
	}
	int_list_append(ilist, val);
    }
    return true;
}

/* 
 * Read single clause in CNF file
 * Result stored in integer list
 * Return value = true if successful
 * If error occurs, a diagnostic message is written to err_buf (up to maxlen characters)
 */
bool get_cnf_clause(rio_t *rp, int_list_t *ilist, char *err_buf, size_t maxlen) {
    char buf[12];
    int rc = 0;
    int val = 0;
    uint8_t sep;
    int_list_reset(ilist);
    /* Skip comments */
    while (true) {
	rc = rio_read_token(rp, (uint8_t *) buf, 12, &sep);
	if (rc == 0)
	    return true;
	if (rc < 0) {
	    snprintf(err_buf, maxlen, "Line %zd.  Error reading file", rp->line_cnt);
	    return false;
	}
	if (strcmp(buf, done_text) == 0)
	    return true;
	if (buf[0] == 'c') {
	    if ((char) sep != '\n') {
		rc = rio_skip_line(rp);
		if (rc == 0)
		    return true;
		if (rc < 0) {
		    snprintf(err_buf, maxlen, "Line %zd.  Error reading comment", rp->line_cnt);
		    return false;
		}
	    }
	} else
	    break;
    }
    if (sscanf(buf, "%d", &val) != 1) {
	snprintf(err_buf, maxlen, "Line %zd.  Invalid initial integer", rp->line_cnt);
	return false;
    }
    int_list_append(ilist, val);
    if (val != 0) {
	rc = rio_read_int_list_text(rp, ilist);
	if (rc < 0) {
	    snprintf(err_buf, maxlen, "Line %zd.  Error reading file", rp->line_cnt);
	    return false;
	}
    }
    return true;
}

/* 
 * Read single clause in text representation of a proof
 * Result stored in integer list
 * First element is step number.
 * Second element is either 'a' (add clause) or 'd' (delete clauses)
 * For add, rest of list contains [literals 0 antecedentIds 0]
 * For delete, rest of list contains [clauseIds 0]
 * Return value = true if successful
 * If encounter EOF, resulting integer list is of length 0
 * If error occurs, a diagnostic message is written to err_buf (up to maxlen characters)
 */
static bool get_text_proof_clause(rio_t *rp, int_list_t *ilist, char *err_buf, size_t maxlen) {
    char buf[12];
    int rc = 0;
    int val;
    size_t i;
    /* Default is to add */
    int nzero = 2;
    uint8_t sep = 0;
    int_list_reset(ilist);
    for (i = 0; i < nzero; i++) {
	/* Skip comments */
	while (true) {
	    rc = rio_read_token(rp, (uint8_t *) buf, 12, &sep);
	    if (rc == 0)
		return true;
	    if (rc < 0) {
		snprintf(err_buf, maxlen, "Line %zd.  Error reading file", rp->line_cnt);
		return false;
	    }
	    if (buf[0] == 'c') {
		if ((char) sep != '\n') {
		    rc = rio_skip_line(rp);
		    if (rc == 0)
			return true;
		    if (rc < 0) {
			snprintf(err_buf, maxlen, "Line %zd.  Error reading comment", rp->line_cnt);
			return false;
		    }
		}
	    } else
		break;
	}
	if (sscanf(buf, "%d", &val) != 1) {
	    snprintf(err_buf, maxlen, "Line %zd.  Invalid initial integer", rp->line_cnt);
	    return false;
	}
	int_list_append(ilist, val);
	if (i == 0) {
	    rc = rio_read_token(rp, (uint8_t *) buf, 12, NULL);
	    if (rc <= 0) {
		snprintf(err_buf, maxlen, "Line %zd.  Error reading file", rp->line_cnt);
		return false;
	    }
	    if (buf[0] == 'd') {
		int_list_append(ilist, 'd');
		/* Don't need second pass */
		nzero = 1;
	    } else {
		int_list_append(ilist, 'a');
		if (sscanf(buf, "%d", &val) != 1) {
		    snprintf(err_buf, maxlen, "Line %zd.  Invalid integer", rp->line_cnt);
		    return false;
		}
		int_list_append(ilist, val);
	    }
	}
	if (val != 0) {
	    rc = rio_read_int_list_text(rp, ilist);
	    if (rc < 0) {
		snprintf(err_buf, maxlen, "Line %zd.  Error reading file", rp->line_cnt);
		return false;
	    }
	}
    }
    return true;
}

/* 
 * Read single clause in binary representation of a proof
 * Result stored in integer list
 * First element is step number.
 * Second element is either 'a' (add clause) or 'd' (delete clauses)
 * For add, rest of list contains [literals 0 antecedentIds 0]
 * For delete, rest of list contains [clauseIds 0]
 * Return value = true if successful
 * If encounter EOF, resulting integer list is of length 0
 * If error occurs, a diagnostic message is written to err_buf (up to maxlen characters)
 */
static bool get_binary_proof_clause(rio_t *rp, int_list_t *ilist, char *err_buf, size_t maxlen) {
    int nzero = 2;
    int i;
    int rc;
    int_list_reset(ilist);
    for (i = 0; i < nzero; i++) {
	rc = rio_read_int_list_binary(rp, ilist);
	if (rc < 0) {
	    snprintf(err_buf, maxlen, "Byte %zd.  Error reading file", rp->byte_cnt);
	    return false;
	}
	if (ilist->count == 0)
	    return true;
	if (ilist->count < 2) {
	    snprintf(err_buf, maxlen, "Byte %zd.  Cannot read proof step.  Only %zd integers",
		     rp->byte_cnt, ilist->count);
	    return false;
	}
	if (ilist->contents[1] == 'd')
	    /* Delete step */
	    nzero = 1;
    }
    return true;
}

/* 
 * Read single clause in text or binary representation of a proof
 * Result stored in integer list
 * First element is step number.
 * Second element is either 'a' (add clause) or 'd' (delete clauses)
 * For add, rest of list contains [literals 0 antecedentIds 0]
 * For delete, rest of list contains [clauseIds 0]
 * Return value = true if successful
 * If encounter EOF, resulting integer list is of length 0
 * If error occurs, a diagnostic message is written to err_buf (up to maxlen characters)
 */
bool get_proof_clause(rio_t *rp, int_list_t *ilist, bool is_binary, char *err_buf, size_t maxlen) {
    if (is_binary)
	return get_binary_proof_clause(rp, ilist, err_buf, maxlen);
    else
	return get_text_proof_clause(rp, ilist, err_buf, maxlen);
}


/******************************** 
 * Client/server helper functions
 ********************************/
/*
 * open_clientfd - Open connection to server at <hostname, port> and
 *     return a socket descriptor ready for reading and writing. This
 *     function is reentrant and protocol-independent.
 *
 *     On error, returns: 
 *       -2 for getaddrinfo error
 *       -1 with errno set for other errors.
 */
int open_clientfd(char *hostname, char *port) {
    int clientfd, rc;
    struct addrinfo hints, *listp, *p;

    /* Get a list of potential server addresses */
    memset(&hints, 0, sizeof(struct addrinfo));
    hints.ai_socktype = SOCK_STREAM;  /* Open a connection */
    hints.ai_flags = AI_NUMERICSERV;  /* ... using a numeric port arg. */
    hints.ai_flags |= AI_ADDRCONFIG;  /* Recommended for connections */
    if ((rc = getaddrinfo(hostname, port, &hints, &listp)) != 0) {
        fprintf(stderr, "getaddrinfo failed (%s:%s): %s\n", hostname, port, gai_strerror(rc));
        return -2;
    }
  
    /* Walk the list for one that we can successfully connect to */
    for (p = listp; p; p = p->ai_next) {
        /* Create a socket descriptor */
        if ((clientfd = socket(p->ai_family, p->ai_socktype, p->ai_protocol)) < 0) 
            continue; /* Socket failed, try the next */

        /* Connect to the server */
        if (connect(clientfd, p->ai_addr, p->ai_addrlen) != -1) 
            break; /* Success */
        if (close(clientfd) < 0) { /* Connect failed, try another */  //line:netp:openclientfd:closefd
            fprintf(stderr, "open_clientfd: close failed: %s\n", strerror(errno));
            return -1;
        } 
    } 

    /* Clean up */
    freeaddrinfo(listp);
    if (!p) /* All connects failed */
        return -1;
    else    /* The last connect succeeded */
        return clientfd;
}

/*  
 * open_listenfd - Open and return a listening socket on port. This
 *     function is reentrant and protocol-independent.
 *
 *     On error, returns: 
 *       -2 for getaddrinfo error
 *       -1 with errno set for other errors.
 */
int open_listenfd(char *port) 
{
    struct addrinfo hints, *listp, *p;
    int listenfd, rc, optval=1;

    /* Get a list of potential server addresses */
    memset(&hints, 0, sizeof(struct addrinfo));
    hints.ai_socktype = SOCK_STREAM;             /* Accept connections */
    hints.ai_flags = AI_PASSIVE | AI_ADDRCONFIG; /* ... on any IP address */
    hints.ai_flags |= AI_NUMERICSERV;            /* ... using port number */
    if ((rc = getaddrinfo(NULL, port, &hints, &listp)) != 0) {
        fprintf(stderr, "getaddrinfo failed (port %s): %s\n", port, gai_strerror(rc));
        return -2;
    }

    /* Walk the list for one that we can bind to */
    for (p = listp; p; p = p->ai_next) {
        /* Create a socket descriptor */
        if ((listenfd = socket(p->ai_family, p->ai_socktype, p->ai_protocol)) < 0) 
            continue;  /* Socket failed, try the next */

        /* Eliminates "Address already in use" error from bind */
        setsockopt(listenfd, SOL_SOCKET, SO_REUSEADDR,    //line:netp:csapp:setsockopt
                   (const void *)&optval , sizeof(int));

        /* Bind the descriptor to the address */
        if (bind(listenfd, p->ai_addr, p->ai_addrlen) == 0)
            break; /* Success */
        if (close(listenfd) < 0) { /* Bind failed, try the next */
            fprintf(stderr, "open_listenfd close failed: %s\n", strerror(errno));
            return -1;
        }
    }


    /* Clean up */
    freeaddrinfo(listp);
    if (!p) /* No address worked */
        return -1;

    /* Make it a listening socket ready to accept connection requests */
    if (listen(listenfd, LISTENQ) < 0) {
        close(listenfd);
	return -1;
    }
    return listenfd;
}
