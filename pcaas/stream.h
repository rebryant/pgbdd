#ifndef __STREAM_H__
#define __STREAM_H__
/* Support for multiple proof file formats and for proof checking server */
#include <stdint.h>
#include <stdarg.h>
#include <stdbool.h>

#include "csapp-subset.h"


/**** Protocol Parameters ******
 Transmission based on sending packet with following format:
 Byte  0: Type.  Currently, support either string or integer list
 Bytes 1-3: Unused
 Bytes 4-7: Payload length (in bytes), stored as unsigned integer in network byte order
 Bytes 8+:  Payload.

 With integer list, store in same format as used to represent literals in binary files:

 * Signed integer --> unsigned integer:
   For x >= 0, represent as 2*x.  For x < 0, represent as 2*(-x)+1
   
 * Unsigned integer --> byte sequence.
   Convert unsigned x to 7-bit words w0, ..., wk, where x = SUM_i wi*(128^i)
   Represent x with byte sequence 1w0, 1w1, ..., 1wk-1, 0wk
*********************************/

/*********** Declarations *************/

/* Supported packet types */
typedef enum { PACKET_STRING, PACKET_ILIST } packet_type_t;

/* Data structure to represent packet and to store compressed representation of integer list */
typedef struct {
    uint8_t type;          // One of packet_type_t values
    uint8_t unused[3];
    uint32_t plength_nbo;  // Number of bytes in payload.  Filled in only when sending/receiving packets
    uint8_t payload[0];    // Byte sequence
} packet_t;

/* Data structure for building packet */
typedef struct {
    size_t plength; /* Payload length */
    size_t alloc_size; /* Number of bytes allocated for entire buffer */
    packet_t *buffer;
} packet_buffer_t;

/* Data structure for representing integer lists */
typedef struct {
    size_t count; /* Number of integers in list */
    size_t alloc_size; /* Number of byte allocated for entire buffer */
    int *contents;
} int_list_t;

/********** Functions for generating packet buffers *********/

/* Generate new buffer.  Give hint about possible length */
packet_buffer_t *packet_buffer_new(packet_type_t type, size_t possible_length);

/* Reset buffer to empty payload */
void packet_buffer_reset(packet_buffer_t *pbuf);

/* Free buffer */
void packet_buffer_free(packet_buffer_t *pbuf);

/* Append bytes to buffer */
bool packet_buffer_append(packet_buffer_t *pbuf, uint8_t *bytes, size_t count);

/* Append formatted string to buffer */
/* If buffer nonempty, overwrites preceding null character and inserts new one at end */
/* Returns net number of new characters */
int bnprintf(packet_buffer_t *pbuf, size_t max_size, const char *format, ...);


/********** Functions for working with integer lists ********/

/* Generate new list.  give hint about possible length */
int_list_t *int_list_new(size_t possible_length);

/* Reset list to be empty */
void int_list_reset(int_list_t *ilist);

/* Free list */
void int_list_free(int_list_t *ilist);

/* Append integer to list */
bool int_list_append(int_list_t *ilist, int value);

/************ Converting between integer lists and other formats *****/
/* All of the following return true for success, false for failure */

/* Convert from buffer to integer list */
/* Contents appended to existing contents */
/* Uses type to determine whether list is in text or compressed form */
bool decode_int_list(packet_buffer_t *pbuf, int_list_t *ilist);

/* Generate compressed representation of integer list */
/* Contents appended to existing contents */
/* Uses type to determine whether list is in text or compressed form */
bool encode_int_list(packet_buffer_t *pbuf, int_list_t *ilist);


/************ Input/Output *****/

/* Like rio_readlineb, but reads text into packet buffer */
/* Buffer empty if hit EOF with no data */
/* Otherwise, buffer terminated with NULL character */
bool packet_buffer_readlineb(rio_t *reader, packet_buffer_t *pbuf);

/* Write packet (e.g., to socket) */
bool packet_buffer_write(int fd, packet_buffer_t *pbuf);

/* 
   Write payload only from packet (e.g., for generating compressed list in file.
   Suitable for either binary or text formats 
*/
bool payload_write(int fd, packet_buffer_t *pbuf);

/* Read packet from buffered file */
bool packet_buffer_read(rio_t *reader, packet_buffer_t *pbuf);

/* Read compressed integer list.   Stop when encounter compressed representation of 0 */
/* Append to existing list */
bool int_list_read_binary(rio_t *reader, int_list_t *ilist);


#endif /* __STREAM_H__ */
