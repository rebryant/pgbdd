/*------------------------------------------------------------------------*/
/* Copyright (c) 2005 - 2010 Armin Biere, Johannes Kepler University.     */
/*------------------------------------------------------------------------*/

#include "config.h"

/*------------------------------------------------------------------------*/

#include <assert.h>
#include <stdio.h>
#include <string.h>
#include <limits.h>

/*------------------------------------------------------------------------*/

#include "bfnum.h"

/*------------------------------------------------------------------------*/
/* This section was really hard to come up with and heavily depends on the
 * assumption that negative numbers are implemented with two-complement.
 */
#define BfUweMantissa_MSB \
  (((unsigned)1) << (sizeof (BfUweExponent)*8 - 1))

#define BfUweMantissa_MAX \
  ((~((unsigned)0)) >> ((sizeof (unsigned) - sizeof (BfUweMantissa))*8))

#define BfUweExponent_MAX \
  ((int) \
  ((~((unsigned)0)) >> (sizeof (unsigned)*8 - sizeof (BfUweExponent)*8 + 1)))

#define BfUweExponent_MIN \
  ((int) \
  ((~((unsigned)0)) << (sizeof (BfUweExponent)*8-1)))

#define BfUnsigned_MSB \
  (~((~((unsigned)0)) >> 1))

/*------------------------------------------------------------------------*/

int
booleforce_is_infinity_uwe (BfUwe n)
{
  return !n.mantissa && n.exponent;
}

/*------------------------------------------------------------------------*/

int
booleforce_is_zero_uwe (BfUwe n)
{
  return !n.mantissa && !n.exponent;
}

/*------------------------------------------------------------------------*/

void
booleforce_check_normalized (BfUwe n)
{
  (void) n;
#ifndef NDEBUG
  if (!booleforce_is_zero_uwe (n) && !booleforce_is_infinity_uwe (n))
    assert (n.mantissa & BfUweMantissa_MSB);
#endif
}

/*------------------------------------------------------------------------*/

static BfUwe
booleforce_zero_uwe (void)
{
  BfUwe res;

  res.mantissa = 0;
  res.exponent = 0;
  assert (booleforce_is_zero_uwe (res));

  return res;
}

/*------------------------------------------------------------------------*/

static BfUwe
booleforce_infinity_uwe (void)
{
  BfUwe res;

  res.mantissa = 0;
  res.exponent = 1;
  assert (booleforce_is_infinity_uwe (res));

  return res;
}

/*------------------------------------------------------------------------*/

void
booleforce_print_uwe (BfUwe n, FILE * file)
{
  unsigned mantissa = n.mantissa;
  int exponent = n.exponent;

  if (booleforce_is_infinity_uwe (n))
    fputs ("infinity", file);
  else if (booleforce_is_zero_uwe (n))
    fputc ('0', file);
  else
    {
      if (exponent >= 0)
	{
	  while (exponent < INT_MAX && !(mantissa & 1))
	    {
	      mantissa >>= 1;
	      exponent++;
	    }
	}
      else if (exponent < 0)
	{
	  while (!(mantissa & 1))
	    {
	      mantissa >>= 1;
	      assert (exponent < INT_MAX);
	      exponent++;
	    }
	}

      if (mantissa == 1 && exponent)
	{
	  fprintf (file, "2^%d", (int) exponent);
	}
      else
	{
	  fprintf (file, "%u", (unsigned) mantissa);
	  if (exponent)
	    fprintf (file, "*2^%d", (int) exponent);
	}
    }
}

/*------------------------------------------------------------------------*/

BfUwe
booleforce_normalize_uwe (BfUwe n)
{
  BfUwe res = n;

  if (res.mantissa)
    {
      while (!(res.mantissa & BfUweMantissa_MSB))
	{
	  res.mantissa <<= 1;
	  res.exponent--;
	}
    }

  booleforce_check_normalized (res);

  return res;
}

/*------------------------------------------------------------------------*/

BfUwe
booleforce_init_uwe (unsigned mantissa, int exponent)
{
  BfUwe res;

#ifndef NDEBUG
  memset (&res, 0, sizeof (res));
  assert (booleforce_is_zero_uwe (res));
#endif
  if (mantissa > BfUweMantissa_MAX)
    return booleforce_infinity_uwe ();

  if (mantissa)
    {
      if (exponent < BfUweExponent_MIN)
	return booleforce_zero_uwe ();

      if (exponent > BfUweExponent_MAX)
	return booleforce_infinity_uwe ();
    }

  res.mantissa = mantissa;
  res.exponent = (!mantissa && exponent) ? 1 : exponent;

  res = booleforce_normalize_uwe (res);

  return res;
}

/*------------------------------------------------------------------------*/

BfUwe
booleforce_add_uwe (BfUwe a, BfUwe b)
{
  BfUweExponent delta;
  BfUwe res, tmp;

  if (booleforce_is_infinity_uwe (a) || booleforce_is_zero_uwe (b))
    return a;

  if (booleforce_is_infinity_uwe (b) || booleforce_is_zero_uwe (a))
    return b;

  assert (a.mantissa & BfUweMantissa_MSB);
  assert (b.mantissa & BfUweMantissa_MSB);

  if (a.exponent != b.exponent)
    {
      if (a.exponent < b.exponent)
	{
	  tmp = a;
	  a = b;
	  b = tmp;
	}

      delta = a.exponent - b.exponent;
      b.exponent += delta;
      b.mantissa >>= delta;
    }

  assert (a.exponent == b.exponent);

  res.exponent = a.exponent;
  res.mantissa = a.mantissa + b.mantissa;

  if (res.mantissa < a.mantissa)
    {
      if (res.exponent == BfUweExponent_MAX)
	return booleforce_infinity_uwe ();

      res.exponent++;
      res.mantissa >>= 1;
      res.mantissa |= BfUweMantissa_MSB;
    }

  booleforce_check_normalized (res);

  return res;
}

/*------------------------------------------------------------------------*/

int
booleforce_cmp_uwe (BfUwe a, BfUwe b)
{
  if (a.mantissa == b.mantissa && a.exponent == b.exponent)
    return 0;

  if (booleforce_is_zero_uwe (a))
    return -1;

  if (booleforce_is_infinity_uwe (a))
    return 1;

  if (booleforce_is_zero_uwe (b))
    return 1;

  if (booleforce_is_infinity_uwe (b))
    return -1;

  if (a.exponent < b.exponent)
    return -1;

  if (a.exponent > b.exponent)
    return 1;

  if (a.mantissa < b.mantissa)
    return -1;

  assert (a.mantissa > b.mantissa);

  return 1;
}

/*------------------------------------------------------------------------*/

BfUwe
booleforce_shift_uwe (BfUwe a, int delta_exponent)
{
  BfUweExponent new_exponent;
  BfUwe res = a;

  new_exponent = res.exponent + delta_exponent;

  if (delta_exponent < 0)
    {
      if (new_exponent > res.exponent)
	return booleforce_zero_uwe ();
    }
  else
    {
      if (new_exponent < res.exponent)
	return booleforce_infinity_uwe ();
    }

  res.exponent = new_exponent;

  return res;
}

/*------------------------------------------------------------------------*/

static void
uweconstants (FILE * file)
{
  fprintf (file,
	   "c msb(mantissa) = %u\n"
	   "c max(mantissa) = %u\n"
	   "c min(exponent) = %d\n"
	   "c max(exponent) = %d\n",
	   (unsigned) BfUweMantissa_MSB,
	   (unsigned) BfUweMantissa_MAX,
	   (int) BfUweExponent_MIN, (int) BfUweExponent_MAX);
}

/*------------------------------------------------------------------------*/

static void
uwezero (FILE * file)
{
  BfUwe a;
  memset (&a, 0, sizeof (a));
  assert (booleforce_is_zero_uwe (a));
  booleforce_print_uwe (a, file);
  fputc ('\n', file);
}

/*------------------------------------------------------------------------*/

static void
uwemax (FILE * file)
{
  fputs ("c ", file);
  booleforce_print_uwe (booleforce_init_uwe
			(BfUweMantissa_MAX, BfUweExponent_MAX), file);
  fputc ('\n', file);
}

/*------------------------------------------------------------------------*/

static void
uweadd (FILE * file, unsigned am, int ae, unsigned bm, int be)
{
  BfUwe a = booleforce_init_uwe (am, ae);
  BfUwe b = booleforce_init_uwe (bm, be);
  BfUwe c = booleforce_add_uwe (a, b);
  booleforce_print_uwe (a, file);
  fputs (" + ", file);
  booleforce_print_uwe (b, file);
  fputs (" = ", file);
  booleforce_print_uwe (c, file);
  fputc ('\n', file);
}

/*------------------------------------------------------------------------*/
/**INDENT-OFF**/

static void uweadd0 (FILE * file) { uweadd (file, 40, 0, 4, 0); }
static void uweadd1 (FILE * file) { uweadd (file, 10, 2, 1, 2); }
static void uweadd2 (FILE * file) { uweadd (file, 7, 29, 1, 29); }
static void uweadd3 (FILE * file) { uweadd (file, 7, -1, 1, -1); }

static void uweinf0 (FILE * file)
{ 
  fputs ("c ", file);
  uweadd (file,
          BfUweMantissa_MAX, BfUweExponent_MAX, 
          BfUweMantissa_MAX, BfUweExponent_MAX);
}

/**INDENT-ON**/
/*------------------------------------------------------------------------*/

static void
uwecmp (FILE * file, unsigned am, int ae, unsigned bm, int be)
{
  BfUwe a = booleforce_init_uwe (am, ae);
  BfUwe b = booleforce_init_uwe (bm, be);
  int cmp = booleforce_cmp_uwe (a, b);
  booleforce_print_uwe (a, file);
  if (cmp < 0)
    fputs (" < ", file);
  else if (cmp > 0)
    fputs (" > ", file);
  else
    fputs (" = ", file);
  booleforce_print_uwe (b, file);
  fputc ('\n', file);
}

/*------------------------------------------------------------------------*/
/**INDENT-OFF**/

static void uwecmp0 (FILE * file) { uwecmp (file, 0, 0, 0, 0); }
static void uwecmp1 (FILE * file) { uwecmp (file, 0, 0, 1, 0); }
static void uwecmp2 (FILE * file) { uwecmp (file, 1, 0, 0, 0); }
static void uwecmp3 (FILE * file) { uwecmp (file, 0, 0, 1, -1); }
static void uwecmp4 (FILE * file) { uwecmp (file, 1, -1, 0, 0); }
static void uwecmp5 (FILE * file) { uwecmp (file, 2, 1, 2, 1); }
static void uwecmp6 (FILE * file) { uwecmp (file, 0, 1, 2, -1); }
static void uwecmp7 (FILE * file) { uwecmp (file, 2, -1, 0, 1); }
static void uwecmp8 (FILE * file) { uwecmp (file, 0, 1, 0, 1); }

/**INDENT-ON**/
/*------------------------------------------------------------------------*/

static void
uweinc (FILE * file)
{
  BfUwe score = booleforce_init_uwe (1, 0);
  BfUwe inc = booleforce_init_uwe (1, 0);
  BfUwe shifted, new_score;
  int count = 0;

  do
    {
      new_score = booleforce_add_uwe (score, inc);

      if (count >= 4)
	fputs ("c ", file);
      booleforce_print_uwe (score, file);
      fputs (" + ", file);
      booleforce_print_uwe (inc, file);
      fputs (" = ", file);
      booleforce_print_uwe (new_score, file);
      fputc ('\n', file);

      score = new_score;

      shifted = booleforce_shift_uwe (inc, -1);
      inc = booleforce_add_uwe (inc, shifted);

    }
  while (count++ < 200);
}


/*------------------------------------------------------------------------*/

#define TC(name) \
  do { \
    if (!strcmp (argv[0], # name)) \
      { \
	res = 0; \
	name (file); \
      } \
  } while (0)

/*------------------------------------------------------------------------*/

int
test_bfnum (int argc, char **argv)
{
  FILE *file;
  int res;

  (void) argc;
  assert (argc == 3);
  assert (!strcmp (argv[1], "-o"));

  file = fopen (argv[2], "w");
  if (!file)
    return 1;

  res = 1;

  TC (uweconstants);

  TC (uwemax);
  TC (uwezero);
  TC (uweadd0);
  TC (uweadd1);
  TC (uweadd2);
  TC (uweadd3);
  TC (uweinf0);
  TC (uwecmp0);
  TC (uwecmp1);
  TC (uwecmp2);
  TC (uwecmp3);
  TC (uwecmp4);
  TC (uwecmp5);
  TC (uwecmp6);
  TC (uwecmp7);
  TC (uwecmp8);
  TC (uweinc);

  fclose (file);

  return res;
}
