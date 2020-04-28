/*------------------------------------------------------------------------*/
/* Copyright (c) 2005 - 2010 Armin Biere, Johannes Kepler University.     */
/*------------------------------------------------------------------------*/

#ifndef BOOLEFORCE_bftime_h_INCLUDED
#define BOOLEFORCE_bftime_h_INCLUDED

#include <stdio.h>

double booleforce_time_stamp (void);
void booleforce_report (double start_time, FILE *, const char *fmt, ...);

#endif
