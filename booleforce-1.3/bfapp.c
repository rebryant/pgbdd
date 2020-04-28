/*------------------------------------------------------------------------*/
/* Copyright (c) 2005 - 2015 Armin Biere, Johannes Kepler University.     */
/*------------------------------------------------------------------------*/

#include "config.h"

/*------------------------------------------------------------------------*/

#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>
#include <stdarg.h>
#include <signal.h>
/*------------------------------------------------------------------------*/

#include "booleforce.h"
#include "bftime.h"
#include "bfio.h"

/*------------------------------------------------------------------------*/

static FILE *output;
static int close_output;
static const char * output_name;

/*------------------------------------------------------------------------*/

static FILE *input;
static const char *input_name;
static int close_input;
static BooleforceInputBuffer input_buffer;

/*------------------------------------------------------------------------*/

static int extended_trace_format;
static const char *trace_file_name;
static const char *variable_core_file_name;
static const char *clausal_core_file_name;

/*------------------------------------------------------------------------*/

static int read_bytes;
static int max_idx;
static int clauses;
static int lineno;

/*------------------------------------------------------------------------*/

static int verbose;
static int check_level;

/*------------------------------------------------------------------------*/

static char output_buffer[100];
static char *buffer_cursor;
static char *end_of_line = output_buffer + 80;
#ifndef NDEBUG
static char *end_of_buffer = output_buffer + sizeof (output_buffer);
#endif

/*------------------------------------------------------------------------*/

#define MAX_ASSUMPTIONS 4
static int assumptions[MAX_ASSUMPTIONS];
static int num_assumptions;

/*------------------------------------------------------------------------*/

static int
next (void)
{
  int res;

  res = next_char_from_buffer (input_buffer);
  if (res == '\n')
    lineno++;

  read_bytes++;

  return res;
}

/*------------------------------------------------------------------------*/

static const char *
parse (void)
{
  int ch, lit, idx, sign, specified_clauses, specified_max_idx;

  clauses = 0;
  max_idx = 0;
  lineno = 1;
  read_bytes = 0;
  sign = 1;
  lit = 0;

  specified_max_idx = -1;
  specified_clauses = -1;

  while ((ch = next ()) != EOF)
    switch (ch)
      {
      case ' ':
      case '\n':
	break;
      case 'p':
	if (specified_max_idx >= 0)
	  return "found two 'p cnf' headers";
	if (next () != ' ')
	  return "expected space after 'p'";
	if (next () != 'c')
	  return "expected 'c' after 'p '";
	if (next () != 'n')
	  return "expected 'n' after 'p c'";
	if (next () != 'f')
	  return "expected 'f' after 'p cn'";
	if (next () != ' ')
	  return "expected space after 'p cnf'";
	ch = next ();
	if (!isdigit (ch))
	  return "expected digit after 'p cnf '";
	specified_max_idx = ch - '0';
	while (isdigit (ch = next ()))
	  specified_max_idx = 10 * specified_max_idx + (ch - '0');
	if (ch != ' ')
	  return "expected space after 'p cnf <max-idx>'";
	ch = next ();
	if (!isdigit (ch))
	  return "expected space after 'p cnf <max-idx> '";
	specified_clauses = ch - '0';
	while (isdigit (ch = next ()))
	  specified_clauses = 10 * specified_clauses + (ch - '0');
	while (ch == '\r' || ch == ' ' || ch == '\t')
	  ch = next ();
	if (ch != '\n')
	  return "expected new line after 'p cnf <max-idx> <num-clauses>'";
	break;
      case 'c':
      READ_UNTIL_END_OF_LINE:
	while ((ch = next ()) != '\n' && ch != EOF)
	  ;
	break;
      case '-':
	sign = -1;
	ch = next ();
	if (!isdigit (ch))
	  return "expected digit after '-'";
	/* 
	 * FALL THROUGH - NO BREAK 
	 */
      case '0':
      case '1':
      case '2':
      case '3':
      case '4':
      case '5':
      case '6':
      case '7':
      case '8':
      case '9':
	if (specified_max_idx < 0)
	  goto HEADER_MISSING;

	if (clauses >= specified_clauses)
	  return "too many clauses";

	idx = ch - '0';
	ch = next ();
	while (isdigit (ch))
	  {
	    idx = 10 * idx + (ch - '0');
	    ch = next ();
	  }

	if (ch == 'c')
	  goto READ_UNTIL_END_OF_LINE;

	if (!isspace (ch))
	  return "expected space or comment after number";

	if (idx > specified_max_idx)
	  return "specified index exceeded";

	if (idx > max_idx)
	  max_idx = idx;
	if (!idx)
	  clauses++;
	lit = sign * idx;
	booleforce_add (lit);
	sign = 1;
	break;
      default:
	return "invalid character";
      }

  if (lit)
    return "missing 0 after last clause";

  if (specified_max_idx < 0)
  HEADER_MISSING:
    return "'p cnf <max-idx> <num-clauses>' header missing";

  assert (max_idx <= specified_max_idx);

  if (clauses < specified_clauses)
    return "clauses missing";

  return 0;
}

/*------------------------------------------------------------------------*/

static int
parse_and_print_parse_error (void)
{
  double start_time = booleforce_time_stamp ();
  const char *err;

  if (verbose)
    {
      fprintf (output, "c parsing %s\n", input_name);
      fflush (output);
    }

  if ((err = parse ()))
    {
      fprintf (output, "%s:%d: %s\n", input_name, lineno, err);
    }
  else if (verbose)
    {
      if (verbose > 1)
	{
	  fprintf (output, "c read %d bytes\n", read_bytes);
	  fprintf (output, "c found maximal index %d\n", max_idx);
	}

      if (verbose)
	booleforce_report (start_time, output,
			   "c parsed %d clauses", clauses);
    }

  fflush (output);

  return !err;
}

/*------------------------------------------------------------------------*/

static void
flush_buffer (void)
{
  assert (output_buffer < buffer_cursor);
  assert (buffer_cursor < end_of_buffer);

  *buffer_cursor = '\0';
  fputs (output_buffer, output);
  fputc ('\n', output);
  buffer_cursor = output_buffer;
}

/*------------------------------------------------------------------------*/

static void
print_int_to_buffer (int n)
{
  char *next_buffer_cursor;
  int len;

REENTER_PRINT_INT_TO_BUFFER:
  if (buffer_cursor == output_buffer)
    *buffer_cursor++ = 'v';

  len = sprintf (buffer_cursor, " %d", n);
  next_buffer_cursor = buffer_cursor + len;

  /* Post mortem check.
   */
  assert (next_buffer_cursor < end_of_buffer);

  if (next_buffer_cursor >= end_of_line)
    {
      flush_buffer ();
      goto REENTER_PRINT_INT_TO_BUFFER;
    }
  else
    buffer_cursor = next_buffer_cursor;
}

/*------------------------------------------------------------------------*/

static void
print_assignment (void)
{
  int i, lit;

  buffer_cursor = output_buffer;
  for (i = 1; i <= max_idx; i++)
    {
      lit = (booleforce_deref (i) > 0) ? i : -i;
      print_int_to_buffer (lit);
    }

  print_int_to_buffer (0);

  if (buffer_cursor > output_buffer)
    flush_buffer ();
}

/*------------------------------------------------------------------------*/

static int
apterr (const char *fmt, ...)
{
  va_list ap;
  fputs ("*** booleforce: ", output);
  va_start (ap, fmt);
  vfprintf (output, fmt, ap);
  va_end (ap);
  fputc ('\n', output);
  fflush (output);
  return 1;
}

/*------------------------------------------------------------------------*/

static int
print_resolution_trace (int extended)
{
  double start_time = booleforce_time_stamp ();
  FILE *file;

  assert (trace_file_name);
  file = booleforce_open_file_for_writing (trace_file_name);
  if (!file)
    return apterr ("can not write resolution trace to '%s'", trace_file_name);

  booleforce_print_resolution_trace (file, extended);
  booleforce_close_file (file);

  if (verbose)
    booleforce_report (start_time, output,
		       "c wrote resolution trace to '%s'", trace_file_name);

  return 0;
}

/*------------------------------------------------------------------------*/

static int
print_variable_core (void)
{
  FILE *file;

  assert (variable_core_file_name);
  file = booleforce_open_file_for_writing (variable_core_file_name);
  if (!file)
    return apterr ("can not write variable core to '%s'",
	           variable_core_file_name);

  (void) booleforce_print_variable_core (file);
  booleforce_close_file (file);

  return 0;
}

/*------------------------------------------------------------------------*/

static int
print_clausal_core (void)
{
  FILE *file;

  assert (clausal_core_file_name);
  file = booleforce_open_file_for_writing (clausal_core_file_name);
  if (!file)
    return apterr ("can not write clausal core to '%s'",
	           clausal_core_file_name);

  (void) booleforce_print_clausal_core (file);
  booleforce_close_file (file);

  return 0;
}

/*------------------------------------------------------------------------*/

#define USAGE \
"usage: booleforce [<option> ...] [<file>[.gz]]\n" \
"\n" \
"where <option> is one of the following options:\n" \
"\n" \
"  -h         print this command line option summary\n" \
"  --version  print booleforce library version and exit\n" \
"  --config   print compile time options and exit\n" \
"\n" \
"  -o <out>   set output file\n" \
"  -v[<inc>]  increase verbose level by <inc> (default 1)\n" \
"  -n         do not print satisfying assignment\n" \
"  -t <out>   generate trace and set trace file\n" \
"  -T <out>   generate trace and set extended trace file\n" \
"  -c <out>   enable variable core generation and set core file\n" \
"  -C <out>   enable clausal core generation and set core file\n" \
"\n" \
"  --conflict-limit=<limit-on-number-of-conflicts>\n" \
"  --decision-limit=<limit-on-number-of-decisions>\n" \
"  --time-limit=<limit-in-seconds>\n" \
"\n" \
"  --assume <lit>{,<lit>}  pre-charge decision heuristic (buggy)\n" \
"\n" \
"  --disable-...   (disable undocumented option)\n" \
"\n" \
"  --print    parse and print input file only\n" \
"  --check[=<inc>]  increase check level by <inc> (default 1)\n" \
"  -s[<seed>] set random number seed (default 0)\n"

/*------------------------------------------------------------------------*/

static void
bfmain_reset (void)
{
  if (close_input)
    booleforce_close_file (input);

  booleforce_reset ();

  fflush (output);
  if (close_output)
    fclose (output);
}

/*------------------------------------------------------------------------*/

static void
bfmain_stats (void)
{
  if (verbose >= 2)
    booleforce_stats (output);
  else
    booleforce_resources (output);
}

/*------------------------------------------------------------------------*/

static void
bfmain_sighandler (int signum)
{
  fprintf (output, "c caught signal(%d)\ns UNKNOWN\n", signum);

  if (verbose)
    bfmain_stats ();

  bfmain_reset ();

  exit (0);
}

/*------------------------------------------------------------------------*/

static void
bfmain_init (void)
{
  output = stdout;
  output_name = "<stdout>";
  close_output = 0;

  input = stdin;
  input_name = "<stdin>";
  close_input = 0;

  extended_trace_format = 0;
  trace_file_name = 0;
  variable_core_file_name = 0;

  verbose = 0;
  check_level = 0;

  num_assumptions = 0;

  booleforce_init ();
}

/*------------------------------------------------------------------------*/

static const char *
match (const char * str, const char * pattern)
{
  const char *p, *q;

  for (p = str, q = pattern; *q && *p == *q; q++, p++)
    ;

  if (*q)
    return 0;

  return p;
}

/*------------------------------------------------------------------------*/

static const char *
match_and_option_rest (const char *str, const char *option)
{
  const char * res;

  if (str[0] != '-' || str[1] != '-')
    return 0;

  if (!(res = match (str + 2, option)))
    return 0;

  if (*res++ != '=')
    return 0;

  return res;
}

/*------------------------------------------------------------------------*/

static int
int_option (const char *str, const char *opt, int *res_ptr)
{
  const char *rest;

  if (!(rest = match_and_option_rest (str, opt)))
    return 0;

  *res_ptr = atoi (rest);	/* TODO check that is a valid int */

  return 1;
}

/*------------------------------------------------------------------------*/

static int
double_option (const char *str, const char *opt, double *res_ptr)
{
  const char *rest;

  if (!(rest = match_and_option_rest (str, opt)))
    return 0;

  *res_ptr = atof (rest);	/* TODO check that is a valid int */

  return 1;
}

/*------------------------------------------------------------------------*/

static int
parse_assumptions (const char * str)
{
  const char * p;
  int sign, lit;
  char ch;

  p = str;

NEXT_ASSUMPTION:

  ch = *p++;
  if (ch == '-')
    {
      ch = *p++;
      sign = -1;
    }
  else
    sign = 1;

  lit = 0;

  if (!isdigit (ch))
    return !apterr ("expected digit at position %d in '%s'", p - str, str);

NEXT_DIGIT:
  lit = 10 * lit;
  lit += ch - '0';
  ch = *p++;

  if (isdigit (ch))
    goto NEXT_DIGIT;

  if (num_assumptions >= MAX_ASSUMPTIONS)
    return !apterr ("maximal number of %d assumptions exceeded", 
	            MAX_ASSUMPTIONS);

  lit *= sign;
  assumptions[num_assumptions++] = lit;

  if (ch == ',')
    goto NEXT_ASSUMPTION;

  if (ch)
    return !apterr ("expected ',' or end of string at position %d in '%s'",
	            p - str, str);

  return 1;
}

/*------------------------------------------------------------------------*/

int
booleforce_main (int argc, char **argv)
{
  int res, i, err, done, print_only, do_not_print_assignment;
  int conflict_limit, decision_limit;
  double time_limit;
  const char * arg;
  unsigned seed;
  FILE *file;

  bfmain_init ();

  res = 0;

  print_only = 0;
  do_not_print_assignment = 0;
  seed = 0;

  err = 0;
  done = 0;

  conflict_limit = -1;
  decision_limit = -1;
  time_limit = -1;

  for (i = 1; !done && !err && i < argc; i++)
    {
      if (!strcmp (argv[i], "-h"))
	{
	  fprintf (output, USAGE);
	  done = 1;
	}
      else if (!strcmp (argv[i], "--config"))
	{
	  fputs (booleforce_configuration (), output);
	  done = 1;
	}
      else if (!strcmp (argv[i], "--version"))
	{
	  fprintf (output, "%s\n", booleforce_version ());
	  done = 1;
	}
      else if (!strcmp (argv[i], "--print"))
	{
	  print_only = 1;
	}
      else if (!strcmp (argv[i], "--assume"))
	{
	  if (++i < argc)
	    {
	      if(!parse_assumptions (argv[i]))
		err = 1;
	    }
	  else
	    err = apterr ("literal argument to '--assume' missing");
	}
      else if ((arg = match (argv[i], "--disable-")))
	{
	  if (!booleforce_disable (arg))
	    goto UNKNOWN_OPTION;
	}
      else if (int_option (argv[i], "conflict-limit", &conflict_limit))
	{
	  /* DO NOTHING */
	}
      else if (int_option (argv[i], "decision-limit", &decision_limit))
	{
	  /* DO NOTHING */
	}
      else if (double_option (argv[i], "time-limit", &time_limit))
	{
	  /* DO NOTHING */
	}
      else if (!strcmp (argv[i], "-n"))
	{
	  do_not_print_assignment = 1;
	}
      else if (argv[i][0] == '-' && argv[i][1] == 'v')
	{
	  if (!argv[i][2])
	    verbose++;
	  else
	    verbose += atoi (argv[i] + 2);
	}
      else if ((arg = match (argv[i], "--check")))
	{
	  if (!arg[0])
	    check_level++;
	  else if (arg[0] != '=')
	    err = apterr ("expected '=' after '--check'");
	  else
	    check_level += atoi (arg + 1);
	}
      else if (argv[i][0] == '-' && argv[i][1] == 's')
	{
	  seed = atoi (argv[i] + 2);
	}
      else if (!strcmp (argv[i], "-o"))
	{
	  if (++i == argc)
	    err = apterr ("missing '-o' argument");
	  else if (!(file = fopen (argv[i], "w")))
	    err = apterr ("can not write '%s'", argv[i]);
	  else if (close_output)
	    {
	      err = apterr ("multiple '-o' options");
	      fclose (file);
	    }
	  else
	    {
	      output = file;
	      output_name = argv[i];
	      close_output = 1;
	    }
	}
      else if (!strcmp (argv[i], "-t") || !strcmp (argv[i], "-T"))
	{
	  if (++i == argc)
	    err = apterr ("missing '-%c' argument", argv[i-1][1]);
	  else if (trace_file_name)
	    err = apterr ("multiple '-t' or '-T' options");
	  else
	    trace_file_name = argv[i];

	  assert (!extended_trace_format);
	  extended_trace_format = (argv[i-1][1] == 'T');
	}
      else if (!strcmp (argv[i], "-c"))
	{
	  if (++i == argc)
	    err = apterr ("missing '-c' argument");
	  else if (variable_core_file_name)
	    err = apterr ("multiple '-c' options");
	  else
	    variable_core_file_name = argv[i];
	}
      else if (!strcmp (argv[i], "-C"))
	{
	  if (++i == argc)
	    err = apterr ("missing '-C' argument");
	  else if (clausal_core_file_name)
	    err = apterr ("multiple '-C' options");
	  else
	    clausal_core_file_name = argv[i];
	}
      else if (argv[i][0] == '-')
UNKNOWN_OPTION:
	err = apterr ("unknown option '%s'", argv[i]);
      else if (close_input)
	err = apterr ("multiple input files");
      else
	{
	  file = booleforce_open_file_for_reading (argv[i]);
	  if (file)
	    {
	      input_name = argv[i];
	      input = file;
	      close_input = 1;
	    }
	  else
	    err = apterr ("can not read '%s'", argv[i]);
	}
    }


  if (!err && !done)
    {
      init_buffer (input_buffer, input);
      booleforce_set_output (output, output_name);
      booleforce_set_verbose (verbose);
      booleforce_set_conflict_limit (conflict_limit);
      booleforce_set_decision_limit (decision_limit);
      booleforce_set_time_limit (time_limit);
      booleforce_set_check (check_level);
      booleforce_set_seed (seed);

      if (trace_file_name || 
	  variable_core_file_name ||
	  clausal_core_file_name ||
	  check_level)
	booleforce_set_trace (1);

      if (verbose)
	{
	  booleforce_banner ();
	  if (verbose >= 2)
	    booleforce_options ();
	}
    }

  if (!err && !done && parse_and_print_parse_error ())
    {
      if (print_only)
	{
	  booleforce_print (output);
	}
      else
	{
	  void *old_sighandler = signal (SIGINT, bfmain_sighandler);

	  for (i = 0; i < num_assumptions; i++)
	    booleforce_assume (assumptions[i]);	/* FIXME: return code? */

	  res = booleforce_sat ();

	  signal (SIGINT, old_sighandler);

	  if (res == BOOLEFORCE_UNSATISFIABLE)
	    {
	      fprintf (output, "s UNSATISFIABLE\n");

	      if (!err && trace_file_name)
		err = print_resolution_trace (extended_trace_format);

	      if (!err && variable_core_file_name)
		err = print_variable_core ();

	      if (!err && clausal_core_file_name)
		err = print_clausal_core ();
	    }
	  else if (res == BOOLEFORCE_SATISFIABLE)
	    {
	      fprintf (output, "s SATISFIABLE\n");
	      if (!do_not_print_assignment)
		print_assignment ();
	    }
	  else
	    {
	      assert (res == BOOLEFORCE_UNKNOWN);
	      fprintf (output, "s UNDECIDED\n");
	    }
	}

      if (verbose)
	bfmain_stats ();
    }

  bfmain_reset ();

  return res;
}
