#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <ctype.h>
#include <arpa/inet.h>

#include "stream.h"


/* Local Declarations */
/* Max number of bytes to encode an int */
#define ELENGTH 5
/* Minimum allocation */
#define MIN_ALLOC 64
/* How much should each allocation increase the overall amount */
#define REALLOC_RATIO 1.414

/* Routines for manipulating byte representations of binary data */

/* Read byte sequence to get integer value */
/* Return number of bytes read, or -1 if invalid */
static int bytes2int(uint8_t *bytes, int *value, int maxbytes) {
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
/* Array bytes must be of length >= ELENGTH */
/* Return length of encoded value */
static int int2bytes(uint8_t *bytes, int value) {
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

/* Convert from string representation of integer to integer */
/* 
   Skip over initial white space.  
   Stop when hit non-digit, and then consume white space + null terminator
*/
static int chars2int(uint8_t *bytes, int *value, int maxbytes) {
    unsigned uval = 0;
    bool neg = false;
    bool skipwhite = true;
    bool firstchar = true;
    bool readdigit = false;
    int count = 0;
    while (count < maxbytes) {
	char c = bytes[count++];
	if (skipwhite) {
	    if (isspace(c))
		continue;
	    else
		skipwhite = false;
	}
	if (firstchar && c == '-') {
	    neg = true;
	    firstchar = false;
	    continue;
	}
	firstchar = false;
	if (isdigit(c)) {
	    unsigned dig = c - '0';
	    if (((uval * 10) / 10) != uval)
		/* Would overflow */
		return -1;
	    uval = (uval * 10) + dig;
	    readdigit = true;
	    continue;
	}
	/* Non-digit encountered.  Back up count */
	count--;
	break;
    }
    /* Make sure OK */
    if (!readdigit)
	return false;
    int mag = (int) uval;
    *value = neg ? -mag : mag;
    /* Skip trailing white space and null terminator */
    while (count < maxbytes) {
	char c = bytes[count++];
	if (isspace(c))
	    continue;
	if (c == '\0')
	    break;
	count--;
	break;
    }
    return count;
}


/**** Protocol Parameters ******
 Transmission based on sending packet with following format:
 Byte  0: Type.  Currently, support either string or integer list
 Bytes 1-3: Unused
 Bytes 4-7: Payload length (in bytes), stored as unsigned integer in network byte order
 Bytes 8+:  Payload.

 With integer list, store in same format as used to represent literals in binary files:

 * Signed integer --> unsigned integer:
   For x >= 0, represent as 2*x.  For x < 0, represent as 2*-x+1
   
 * Unsigned integer --> byte sequence.
   Convert unsigned x to 7-bit words w0, ..., wk, where x = SUM_i wi*(128^i)
   Represent x with byte sequence 1w0, 1w1, ..., 1wk-1, 0wk
*********************************/

/********** Local  Functions for generating packet buffers *********/

/* See if buffer is big enough to hold add more bytes.
   If not, attempt to expand buffer
*/
static bool packet_buffer_check_size(packet_buffer_t *pbuf, size_t add) {
    size_t current = sizeof(packet_t) + pbuf->plength;
    size_t need = current + add;
    if (need > pbuf->alloc_size) {
	size_t min_size = (size_t) (REALLOC_RATIO * current);
	if (need < min_size)
	    need = min_size;
	pbuf->buffer = realloc(pbuf->buffer, need);
	if (pbuf->buffer == NULL)
	    return false;
	pbuf->alloc_size = need;
    }
    return true;
}

/********** Exported  Functions for generating packet buffers *********/

/* Generate new buffer->  Give hint about possible length */
packet_buffer_t *packet_buffer_new(packet_type_t type, size_t possible_length) {
    packet_buffer_t *pbuf = malloc(sizeof(packet_buffer_t));
    if (pbuf == NULL)
	return NULL;
    possible_length += sizeof(packet_t);
    if (possible_length < MIN_ALLOC)
	possible_length = MIN_ALLOC;
    pbuf->buffer = malloc(possible_length);
    if (pbuf->buffer == NULL) {
	free(pbuf);
	return NULL;
    }
    memset(pbuf->buffer, 0, sizeof(packet_t));
    pbuf->buffer->type = type;
    pbuf->plength = 0;
    pbuf->alloc_size = possible_length;
    return pbuf;
}

/* Reset buffer to empty payload */
void packet_buffer_reset(packet_buffer_t *pbuf) {
    pbuf->plength = 0;
}

/* Free buffer */
void packet_buffer_free(packet_buffer_t *pbuf) {
    free(pbuf->buffer);
    free(pbuf);
}

/* Append bytes to buffer */
bool packet_buffer_append(packet_buffer_t *pbuf, uint8_t *bytes, size_t count) {
    if (!packet_buffer_check_size(pbuf, count))
	return false;
    memcpy(&pbuf->buffer->payload[pbuf->plength], bytes, count);
    pbuf->plength += count;
    return true;
}

/* Append formatted string to buffer */
/* Returns number of characters added */
int bnprintf(packet_buffer_t *pbuf, size_t max_size, const char *format, ...) {
    va_list ap;
    if (!packet_buffer_check_size(pbuf, max_size))
	return false;
    va_start(ap, format);
    size_t offset = pbuf->plength;
    int count = 0;
    if (offset > 0 && pbuf->buffer->payload[offset-1] == 0) {
	/* Take away terminator */
	offset--;
	count--;
    }
    /* Account for terminating null */
    count += vsnprintf((char *) &pbuf->buffer->payload[offset], max_size, format, ap) + 1;
    pbuf->plength += count;
    return count;    
}


/********** Local functions for working with integer lists ********/

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

/************ Converting between integer lists and other formats *****/
/* All of the following return true for success, false for failure */

/* Convert from binary buffer to integer list */
/* Contents appended to existing contents */
static bool decode_int_list_binary(packet_buffer_t *pbuf, int_list_t *ilist) {
    size_t offset = 0;
    size_t plength = pbuf->plength;
    while (offset < plength) {
	int val;
	int count = bytes2int(&pbuf->buffer->payload[offset], &val, plength-offset);
	if (count < 0)
	    return false;
	offset += count;
	int_list_append(ilist, val);
    }
    return true;
}

/* Convert from text buffer to integer list */
/* Contents appended to existing contents */
static bool decode_int_list_text(packet_buffer_t *pbuf, int_list_t *ilist) {
    size_t offset = 0;
    size_t plength = pbuf->plength;
    while (offset < plength) {
	int val;
	int count = chars2int(&pbuf->buffer->payload[offset], &val, plength-offset);
	if (count < 0)
	    return false;
	offset += count;
	int_list_append(ilist, val);
    }
    return true;
}

/* Convert from buffer to integer list */
/* Detect whether text or binary based on packet type */
/* Contents appended to existing contents */
bool decode_int_list(packet_buffer_t *pbuf, int_list_t *ilist) {
    if (pbuf->buffer->type == PACKET_ILIST)
	return decode_int_list_binary(pbuf, ilist);
    if (pbuf->buffer->type == PACKET_STRING)
	return decode_int_list_text(pbuf, ilist);
    return false;
}

/* Generate compressed representation of integer list */
/* Contents appended to existing contents */
static bool encode_int_list_binary(packet_buffer_t *pbuf, int_list_t *ilist) {
    uint8_t bytes[ELENGTH];
    size_t i;
    for (i = 0; i < ilist->count; i++) {
	size_t count = int2bytes(bytes, ilist->contents[i]);
	if (!packet_buffer_append(pbuf, bytes, count))
	    return false;
    }
    return true;
}

/* Generate text representation of integer list */
/* Contents appended to existing contents */
static bool encode_int_list_text(packet_buffer_t *pbuf, int_list_t *ilist) {
    size_t i;
    for (i = 0; i < ilist->count; i++) {
	int count = bnprintf(pbuf, 10, " %d", ilist->contents[i]);
	if (count == 0)
	    return false;
    }
    bnprintf(pbuf, 2, "\n");
    return true;
}

bool encode_int_list(packet_buffer_t *pbuf, int_list_t *ilist) {
    if (pbuf->buffer->type == PACKET_ILIST)
	return encode_int_list_binary(pbuf, ilist);
    if (pbuf->buffer->type == PACKET_STRING)
	return encode_int_list_text(pbuf, ilist);
    return false;
}

/************ Input/Output *****/

/* Write packet (e.g., to socket) */
bool packet_buffer_write(int fd, packet_buffer_t *pbuf) {
    /* Fix up packet */
    pbuf->buffer->plength_nbo = htonl(pbuf->plength);
    size_t length = pbuf->plength + sizeof(packet_t);
    ssize_t count = rio_writen(fd, (void *) pbuf->buffer, length);
    return count == length;
}

/* Write payload only from packet (e.g., for generating compressed list in file */
bool payload_write(int fd, packet_buffer_t *pbuf) {
    size_t length = pbuf->plength;
    ssize_t count = rio_writen(fd, (void *) pbuf->buffer->payload, length);
    return count == length;
}

/* Read packet from buffered file */
bool packet_buffer_read(rio_t *reader, packet_buffer_t *pbuf) {
    packet_buffer_reset(pbuf);
    size_t hlength = sizeof(packet_t);
    if (rio_readnb(reader, (void *) pbuf->buffer, hlength) != hlength)
	return false;
    size_t plength = (size_t) ntohl(pbuf->buffer->plength_nbo);
    if (!packet_buffer_check_size(pbuf, plength))
	return false;
    if (rio_readnb(reader, (void *) pbuf->buffer->payload, plength) != plength)
	return false;
    return true;
}

/* Read byte sequence to get integer value */
/* Return number of bytes read, or -1 if invalid */
static bool read_binary_int(rio_t *reader, int *value, bool *eofp) {
    unsigned int uval = 0;
    bool done = false;
    unsigned weight = 0;
    int rc = 0;
    int count = 0;

    while (!done) {
	uint8_t nbyte;
	if ((rc = rio_readnb(reader, (void *) &nbyte, 1)) !=1)
	    break;
	count++;
	uint8_t bval = (nbyte) & 0x7F;
	uint8_t hval = (nbyte>>7) & 0x1;
	if (weight >= 32 || ((bval << weight) >> weight) != bval)
	    /* Value would overflow */
	    return false;
	uval += bval << weight;
	weight += 7;
	done = (hval != 1);
    }
    *eofp = rc == 0;
    if (!done) {
	/* OK if EOF and no bytes read */
	return rc == 0 && count == 0;
    }
    int sign = uval & 0x1;
    int mag = (uval >> 1);
    *value = sign ? -mag : mag;
    return true;
}

/* Read compressed integer list into buffer.  Stop when encounter compressed representation of 0 */
/* Append to existing  buffer */
bool int_list_read_binary(rio_t *reader, int_list_t *ilist) {
    int value;
    bool eof = false;
    while (read_binary_int(reader, &value, &eof)) {
	if (eof)
	    return true;
	int_list_append(ilist, value);
	if (value == 0)
	    return true;
    }
    return false;
}

/* 
 * Like rio_readlineb, but reads into packet buffer
 */
bool packet_buffer_readlineb(rio_t *rp, packet_buffer_t *pbuf) 
{
    int rc;
    int n = 0;
    uint8_t byte;
    packet_buffer_reset(pbuf);
    while (true) {
        if ((rc = rio_readnb(rp, (char *) &byte, 1)) == 1) {
	    if (!packet_buffer_append(pbuf, &byte, 1))
		return false;
	    n++;
	    if (byte == '\n')
     		break;
	} else if (rc == 0) {
	    if (n == 0)
		return true; /* EOF, no data read.  Not error */
	    else
		break;      /* EOF, some data was read */
	} else
	    return false;  /* Error */
    }
    /* Terminate string */
    byte = 0;
    return packet_buffer_append(pbuf, &byte, 1);
}


