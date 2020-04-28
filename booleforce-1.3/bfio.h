/*------------------------------------------------------------------------*/
/* Copyright (c) 2005 - 2010 Armin Biere, Johannes Kepler University.     */
/*------------------------------------------------------------------------*/

#ifndef BOOLEFORCE_bfio_h_INCLUDED
#define BOOLEFORCE_bfio_h_INCLUDED

/*------------------------------------------------------------------------*/

#include <stdio.h>

/*------------------------------------------------------------------------*/
/* transparent usage of 'gzipped' files 
 */
FILE *booleforce_open_file_for_reading (const char *file_name);
FILE *booleforce_open_file_for_writing (const char *file_name);
void booleforce_close_file (FILE * file);

/*------------------------------------------------------------------------*/

#define BOOLEFORCE_BUFFER_SIZE (1 << 14)

typedef struct BooleforceInputBuffer BooleforceInputBuffer;

struct BooleforceInputBuffer
{
  unsigned char *next;
  unsigned char *end;
  FILE *file;
  unsigned char start[BOOLEFORCE_BUFFER_SIZE];
};

/*------------------------------------------------------------------------*/

#define init_buffer(buffer,f) \
  do { \
    (buffer).file = (f); \
    (buffer).next = 0; \
    (buffer).end = 0; \
  } while(0)

/*------------------------------------------------------------------------*/

int booleforce_fill_buffer (BooleforceInputBuffer *);

/*------------------------------------------------------------------------*/

#define next_char_from_buffer(buffer) \
  (((buffer).next == (buffer).end) ? \
      booleforce_fill_buffer (&(buffer)) : *(buffer).next++)

/*------------------------------------------------------------------------*/
#endif
