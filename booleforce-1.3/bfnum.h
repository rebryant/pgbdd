/*------------------------------------------------------------------------*/
/* Copyright (c) 2005 - 2010 Armin Biere, Johannes Kepler University.     */
/*------------------------------------------------------------------------*/

#ifndef BOOLEFORCE_bfnum_h_INCLUDED
#define BOOLEFORCE_bfnum_h_INCLUDED

/*------------------------------------------------------------------------*/

#include <stdio.h>

/*------------------------------------------------------------------------*/

typedef struct BfUwe BfUwe;

/*------------------------------------------------------------------------*/

#define BfUweMantissa unsigned short
#define BfUweExponent signed short

/*------------------------------------------------------------------------*/

struct BfUwe
{
  BfUweMantissa mantissa;
  BfUweExponent exponent;
};

/*------------------------------------------------------------------------*/

BfUwe booleforce_init_uwe (unsigned mantissa, int exponent);
BfUwe booleforce_shift_uwe (BfUwe, int);
int booleforce_is_infinity_uwe (BfUwe);
int booleforce_is_zero_uwe (BfUwe);
BfUwe booleforce_add_uwe (BfUwe, BfUwe);
void booleforce_print_uwe (BfUwe, FILE *);
int booleforce_cmp_uwe (BfUwe, BfUwe);

/*------------------------------------------------------------------------*/
#endif
