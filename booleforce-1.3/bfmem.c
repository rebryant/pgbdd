/*------------------------------------------------------------------------*/
/* Copyright (c) 2005 - 2010 Armin Biere, Johannes Kepler University.     */
/*------------------------------------------------------------------------*/

#include "config.h"

/*------------------------------------------------------------------------*/

#include <assert.h>
#include <stdlib.h>
#include <string.h>

/*------------------------------------------------------------------------*/

#include "bfmem.h"

/*------------------------------------------------------------------------*/

#include "booleforce.h"

/*------------------------------------------------------------------------*/

static size_t current_bytes;
static size_t max_bytes;

/*------------------------------------------------------------------------*/

void
booleforce_reset_mem (void)
{
  /* USUALY ALL HEAP MEMORY SHOULD HAVE BEEN FREED */

  assert (getenv ("LEAK") || !current_bytes);

  current_bytes = 0;
  max_bytes = 0;
}

/*------------------------------------------------------------------------*/

void *
booleforce_new (size_t size)
{
  size_t real_size, *res;

  assert (size);

  real_size = size;
#ifndef NDEBUG
  real_size += sizeof (size_t);
#endif
  res = malloc (real_size);
  assert (res);
#ifndef NDEBUG
  *res++ = size;
#endif
  current_bytes += size;
  memset (res, 0, size);

  if (current_bytes > max_bytes)
    max_bytes = current_bytes;

  return res;
}

/*------------------------------------------------------------------------*/

void
booleforce_delete (void *ptr, size_t size)
{
#ifndef NDEBUG
  size_t real_size;
#endif
  size_t *real_ptr;

  if (ptr)
    {
      real_ptr = ptr;
#ifndef NDEBUG
      real_size = size + sizeof (size_t);
      real_ptr--;
      assert (*real_ptr == size);
#endif
      assert (current_bytes >= size);
      current_bytes -= size;
#ifndef NDEBUG
      memset (real_ptr, 0, real_size);
#endif
      free (real_ptr);
    }
  else
    assert (!size);
}

/*------------------------------------------------------------------------*/

void *
booleforce_enlarge (void *ptr, size_t old_size, size_t new_size)
{
  size_t real_size, *res;

  if (!ptr)
    {
      assert (!old_size);
      return booleforce_new (new_size);
    }

  res = ptr;
  real_size = new_size;
#ifndef NDEBUG
  real_size += sizeof (*res);
  assert (old_size);
  res--;
  assert (*res == old_size);
#endif
  assert (current_bytes >= old_size);
  current_bytes -= old_size;
  current_bytes += new_size;
  res = realloc (res, real_size);
  assert (res);
#ifndef NDEBUG
  *res++ = new_size;
#endif
  if (new_size > old_size)
    memset (((char *) res) + old_size, 0, new_size - old_size);

  if (current_bytes > max_bytes)
    max_bytes = current_bytes;

  return res;
}

/*------------------------------------------------------------------------*/

void
booleforce_delete_ints (int *a)
{
  const int *p;
  size_t bytes;

  for (p = a; *p; p++)
    ;

  bytes = p - a + 1;
  bytes *= sizeof (*a);

  booleforce_delete (a, bytes);
}

/*------------------------------------------------------------------------*/

size_t
booleforce_max_bytes (void)
{
  size_t res;
  res = max_bytes;
  return res;
}

/*------------------------------------------------------------------------*/

size_t
booleforce_current_bytes (void)
{
  size_t res;
  res = current_bytes;
  return res;
}

/*------------------------------------------------------------------------*/

int *
booleforce_intcpy (const int *src, unsigned count)
{
  unsigned i;
  int *res;

  res = booleforce_new ((count + 1) * sizeof (*res));

  for (i = 0; i < count; i++)
    res[i] = src[i];

  res[count] = 0;

  return res;
}

/*------------------------------------------------------------------------*/

char *
booleforce_strdup (const char *str)
{
  char *res;

  assert (str);
  res = booleforce_new (strlen (str) + 1);
  strcpy (res, str);

  return res;
}

/*------------------------------------------------------------------------*/

void
booleforce_delstr (char *str)
{
  assert (str);
  booleforce_delete (str, strlen (str) + 1);
}
