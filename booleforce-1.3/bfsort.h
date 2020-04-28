/*------------------------------------------------------------------------*/
/* Copyright (c) 2005 - 2010 Armin Biere, Johannes Kepler University.     */
/*------------------------------------------------------------------------*/

#ifndef BOOLEFORCE_sort_h_INCLUDED
#define BOOLEFORCE_sort_h_INCLUDED
/*------------------------------------------------------------------------*/
/* This is a generic inlinable 'quicksort' routine, which should be faster
 * than the standard library implementation. The main purpose however is to
 * be deterministic with respect to varying implementations on different
 * platforms.  The basic idea is taken from Sedgewick's algorithm book.
 *
 * The user is only supposed to see 'booleforce_sort'.
 *
 * The 'inlining' of the sorting function allows to inline the comparison
 * function as well.  It uses an externally provided 'stack' to avoid
 * recursion.  The stack can be reused for subsequent calls, which allows
 * reusing the stack memory as well.
 *
 * NOTE: the checker 'booleforce_check_sorted' currently enforces that
 * arrays to be sorted do not contain the same element modulo the comparison
 * function twice.  This is not necessary for the correctness of the code
 * but automatically enforces stable and thus deterministic usages only.
 */
/*------------------------------------------------------------------------*/

#include "bfmem.h"		/* "bfstack.h" needs it */
#include "bfstack.h"		/* will manipulate stacks */

/*------------------------------------------------------------------------*/

#define BOOLEFORCE_INSERTION_SORT_LIMIT 10

/*------------------------------------------------------------------------*/

#define booleforce_internal_sorting_swap(T,p,q) \
do { \
  T tmp = *(q); \
  *(q) = *(p); \
  *(p) = tmp; \
} while (0)

/*------------------------------------------------------------------------*/

#define booleforce_internal_sorting_cmpswap(T,cmp,p,q) \
do { \
  if ((cmp) (*(p), *(q)) > 0) \
    booleforce_internal_sorting_swap (T, p, q); \
} while(0)

/*------------------------------------------------------------------------*/

#define booleforce_internal_quicksort_partition(T,cmp,a,l,r) \
do { \
  T pivot; \
  int j; \
  i = (l) - 1; 			/* result in 'i' */ \
  j = (r); \
  pivot = (a)[j]; \
  for (;;) \
    { \
      while ((cmp) ((a)[++i], pivot) < 0) \
	; \
      while ((cmp) (pivot, (a)[--j]) < 0) \
        if (j == (l)) \
	  break; \
      if (i >= j) \
	break; \
      booleforce_internal_sorting_swap (T, (a) + i, (a) + j); \
    } \
  booleforce_internal_sorting_swap (T, (a) + i, (a) + (r)); \
} while(0)

/*------------------------------------------------------------------------*/

#define booleforce_internal_quicksort(T,cmp,a,n,stack) \
do { \
  int l = 0, r = (n) - 1, m, ll, rr, i; \
  assert (empty_stack(stack)); \
  if (r - l <= BOOLEFORCE_INSERTION_SORT_LIMIT) \
    break; \
  for (;;) \
    { \
      m = (l + r) / 2; \
      booleforce_internal_sorting_swap (T, (a) + m, (a) + r - 1); \
      booleforce_internal_sorting_cmpswap (T, cmp, (a) + l, (a) + r - 1); \
      booleforce_internal_sorting_cmpswap (T, cmp, (a) + l, (a) + r); \
      booleforce_internal_sorting_cmpswap (T, cmp, (a) + r - 1, (a) + r); \
      booleforce_internal_quicksort_partition (T, cmp, (a), l + 1, r - 1); \
      if (i - l < r - i) \
	{ \
	  ll = i + 1; \
	  rr = r; \
	  r = i - 1; \
	} \
      else \
	{ \
	  ll = l; \
	  rr = i - 1; \
	  l = i + 1; \
	} \
      if (r - l > BOOLEFORCE_INSERTION_SORT_LIMIT) \
	{ \
	  assert (rr - ll > BOOLEFORCE_INSERTION_SORT_LIMIT); \
	  push_stack (stack, ll); \
	  push_stack (stack, rr); \
	} \
      else if (rr - ll > BOOLEFORCE_INSERTION_SORT_LIMIT) \
        { \
	  l = ll; \
	  r = rr; \
	} \
      else if (count_stack (stack)) \
	{ \
	  r = pop_stack (stack); \
	  l = pop_stack (stack); \
	} \
      else \
	break; \
    } \
} while (0)

/*------------------------------------------------------------------------*/

#define booleforce_internal_insertion_sort(T,cmp,a,n) \
do { \
  T pivot; \
  int l = 0, r = (n) - 1, i, j; \
  for (i = r; i > l; i--) \
    booleforce_internal_sorting_cmpswap (T, cmp, (a) + i - 1, (a) + i); \
  for (i = l + 2; i <= r; i++)  \
    { \
      j = i; \
      pivot = (a)[i]; \
      while ((cmp) (pivot, (a)[j - 1]) < 0) \
        { \
	  (a)[j] = (a)[j - 1]; \
	  j--; \
	} \
      (a)[j] = pivot; \
    } \
} while (0)

/*------------------------------------------------------------------------*/
#ifdef NDEBUG
/*------------------------------------------------------------------------*/
#define booleforce_check_sorted(cmp,a,n) do { } while(0)
/*------------------------------------------------------------------------*/
#else
/*------------------------------------------------------------------------*/
#define booleforce_check_sorted(cmp,a,n) \
do { \
  int i; \
  for (i = 0; i < (n) - 1; i++) \
    assert ((cmp) ((a)[i], (a)[i + 1]) < 0); /* actually <= */ \
} while(0)
/*------------------------------------------------------------------------*/
#endif
/*------------------------------------------------------------------------*/

#define booleforce_sort(T,cmp,a,n,stack) \
do { \
  T * aa = (a); \
  int nn = (n); \
  booleforce_internal_quicksort (T, cmp, aa, nn, stack); \
  booleforce_internal_insertion_sort (T, cmp, aa, nn); \
  assert (empty_stack (stack)); \
  booleforce_check_sorted (cmp, aa, nn); \
} while (0)

/*------------------------------------------------------------------------*/
#endif
