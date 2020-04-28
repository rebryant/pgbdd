/*------------------------------------------------------------------------*/
/* Copyright (c) 2005 - 2010 Armin Biere, Johannes Kepler University.     */
/*------------------------------------------------------------------------*/

#include "config.h"

#ifdef __MINGW32__
#include <windows.h>
#else
#include <sys/time.h>
#include <sys/resource.h>
#include <sys/unistd.h>
#endif

#include <stdarg.h>

#include "bftime.h"

/*------------------------------------------------------------------------*/

double
booleforce_time_stamp (void)
{
  double res;

  res = 0;
#   ifdef __MINGW32__
  {
    FILETIME tmp[2], u, s;
    __int64 s64, u64;

    if (GetProcessTimes (GetCurrentProcess (), tmp, tmp + 1, &s, &u))
      {
	s64 = s.dwLowDateTime;
	s64 |= (__int64) s.dwHighDateTime << 32;

	u64 = u.dwLowDateTime;
	u64 |= (__int64) u.dwHighDateTime << 32;

	res = (s64 + u64) / 1e7;
      }
  }
#  else
  {
    struct rusage u;

    if (!getrusage (RUSAGE_SELF, &u))
      {
	res += u.ru_utime.tv_sec + 1e-6 * u.ru_utime.tv_usec;
	res += u.ru_stime.tv_sec + 1e-6 * u.ru_stime.tv_usec;
      }
  }
#  endif

  return res;
}

/*------------------------------------------------------------------------*/

void
booleforce_report (double start_time, FILE * file, const char *fmt, ...)
{
  double now, passed;
  va_list ap;

  va_start (ap, fmt);
  vfprintf (file, fmt, ap);
  va_end (ap);

  now = booleforce_time_stamp ();
  passed = now - start_time;
  passed = (passed < 0) ? 0 : passed;

  fprintf (file, " in %.2f seconds\n", passed);
  fflush (file);
}
