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
int rio_read_token(rio_t *rp, uint8_t *usrbuf, size_t maxn) {
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
    if (byte == 0) {
	/* Unget the terminating character so that it will be read again */
	rp->rio_cnt--;
	rp->rio_bufptr--;
    }

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
    int len;
    size_t i;
    if (ilist->count <= start_index)
	return 0;
    len = sprintf(buf, "%d", ilist->contents[start_index]);
    nwritten = rio_writenb(rp, (uint8_t *) buf, len);
    if (nwritten < 0)
	return nwritten;
    for (i = start_index + 1; i < ilist->count; i++) {
	len = sprintf(buf, " %d", ilist->contents[i]);
	nw = rio_writenb(rp, (uint8_t *) buf, len);
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
    unsigned count = 0;
    int rc = 0;
    int value;
    do {
	rc = rio_read_token(rp, (uint8_t *) buf, 10);
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
    uint8_t buf[CINT_LENGTH];
    ssize_t nread = 0;
    unsigned count = 0;
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
