/*------------------------------------------------------------------------*/
/* Copyright (c) 2005 - 2010 Armin Biere, Johannes Kepler University.     */
/*------------------------------------------------------------------------*/

#ifndef BOOLEFORCE_bfmem_h_INCLUDED
#define BOOLEFORCE_bfmem_h_INCLUDED

#include <stdlib.h>		/* 'size_t' */

/*------------------------------------------------------------------------*/

#define BOOLEFORCE_NEW(ptr) \
  do { (ptr) = booleforce_new (sizeof (*(ptr))); } while (0)

/*------------------------------------------------------------------------*/

#define BOOLEFORCE_DELETE(ptr) \
  do { booleforce_delete (ptr, sizeof (*(ptr))); (ptr) = 0; } while(0)

/*------------------------------------------------------------------------*/

#define BOOLEFORCE_NEW_ARRAY(a,size) \
  do { \
    size_t bytes = sizeof ((a)[0]) * (size); \
    (a) = booleforce_new (bytes); \
  } while (0)

/*------------------------------------------------------------------------*/

#define BOOLEFORCE_ENLARGE_ARRAY(p,o,n) \
do { \
  size_t old_bytes = sizeof ((p)[0]) * (o); \
  size_t new_bytes = sizeof ((p)[0]) * (n); \
  (p) = booleforce_enlarge ((p), old_bytes, new_bytes); \
} while(0)

/*------------------------------------------------------------------------*/

#define BOOLEFORCE_DELETE_ARRAY(a,size) \
  do { \
    size_t bytes = sizeof ((a)[0]) * (size); \
    booleforce_delete (a, bytes); \
    (a) = 0; \
  } while(0)

/*------------------------------------------------------------------------*/

void *booleforce_new (size_t bytes);
void booleforce_delete (void *ptr, size_t bytes);
void *booleforce_enlarge (void *ptr, size_t old_bytes, size_t new_bytes);

/*------------------------------------------------------------------------*/

char *booleforce_strdup (const char *);
void booleforce_delstr (char *);

/*------------------------------------------------------------------------*/

int *booleforce_intcpy (const int *src, unsigned count);
void booleforce_delete_ints (int *zero_terminated_array_of_ints);

/*------------------------------------------------------------------------*/

size_t booleforce_max_bytes (void);
size_t booleforce_current_bytes (void);
void booleforce_reset_mem (void);

/*------------------------------------------------------------------------*/

#endif
