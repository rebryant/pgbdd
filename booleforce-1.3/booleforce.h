/*------------------------------------------------------------------------*/
/* Copyright (c) 2005 - 2010 Armin Biere, Johannes Kepler University.     */
/*------------------------------------------------------------------------*/

#ifndef BOOLE_FORCE_INCLUDED
#define BOOLE_FORCE_INCLUDED

/*------------------------------------------------------------------------*/

#include <stdio.h>

/*------------------------------------------------------------------------*/

#define BOOLEFORCE_UNKNOWN 0
#define BOOLEFORCE_SATISFIABLE 10
#define BOOLEFORCE_UNSATISFIABLE 20

/*------------------------------------------------------------------------*/
/* Has to be called before any of the other functions in the API.
 */
void booleforce_init (void);

/*------------------------------------------------------------------------*/
/* Reset the library to a prestine state.  Should also be used if you want
 * to release the memory used by the library.
 */
void booleforce_reset (void);

/*------------------------------------------------------------------------*/
/* Add clauses by adding their literals with 'booleforce_add' and then close
 * the clause by adding '0'.
 */
void booleforce_add (int);

/*------------------------------------------------------------------------*/
/* Add assumptions.
 *
 * TODO: currently you can only use this function to pre charge the decision 
 * heuristics.  The first decisions will be taken according to the order of 
 * assumptions (FIFO = first assumed assumption taken as first decision).
 * If the end of the assumptions is reached, then we switch to the standard 
 * decision heuristic.  Already satisfied assumptions are simply ignored.
 *
 * FIXME: disatisfied assumptions are simply ignored as well.
 */
void booleforce_assume (int);

/*------------------------------------------------------------------------*/
/* Returns 'BOOLEFORCE_TRUE' if formular is satisfiable, 'BOOLEFORCE_FALSE'
 * if formula is unsatisfiable and 'BOOLEFORCE_UNKNOWN' otherwise.
 */
int booleforce_sat (void);

/*------------------------------------------------------------------------*/
/* After 'booleforce_sat' returns 'BOOLEFORCE_SATISFIABLE', this function
 * can be used to extract a satisfying assignment.  The argument is a
 * literal.  The result is larger than zero if the literal is assigned to
 * true, smaller than zero if it is assigned to false, and zero otherwise.
 */
int booleforce_deref (int);

/*------------------------------------------------------------------------*/
/* After 'booleforce_sat' returns 'BOOLEFORCE_UNSATISFIABLE', this function
 * can be used to extract variables that are in the core of the
 * unsatisfiability proof.  This only works if trace generation is enabled
 * with 'booleforce_trace' and trace generation code is included by using
 * './configure --trace'.
 */
int booleforce_var_in_core (int);

/*------------------------------------------------------------------------*/
/* Prints the indices of the variables in the core to the given file.  The
 * number of printed variables is returned or a negative number if an error
 * occurred.
 */
int booleforce_print_variable_core (FILE *);

/*------------------------------------------------------------------------*/
/* Prints the clauses of the the core to the given file.  The number of
 * printed clauses is returned or a negative number denoting an error.
 */
int booleforce_print_clausal_core (FILE *);

/*------------------------------------------------------------------------*/
/* If 'trace generation' is enabled with 'booleforce_trace (1)', then a
 * a resolution trace can be printed.  This only produces a legal trace
 * if trace generation code is included by using './configure --trace'.
 */
void booleforce_print_resolution_trace (FILE *, int extended);

/*------------------------------------------------------------------------*/

void booleforce_set_output (FILE *, const char * name);
void booleforce_set_check (int level);
void booleforce_set_verbose (int level);
void booleforce_set_trace (int enable);
void booleforce_set_seed (unsigned seed);
void booleforce_set_conflict_limit (int limit);
void booleforce_set_decision_limit (int limit);
void booleforce_set_time_limit (double seconds);

/*------------------------------------------------------------------------*/

int booleforce_disable (const char *);

/*------------------------------------------------------------------------*/

void booleforce_banner (void);		/* options version and id */
void booleforce_options (void);		/* dump options */

/*------------------------------------------------------------------------*/

void booleforce_stats (FILE *);
void booleforce_resources (FILE *);
size_t booleforce_max_bytes (void);
size_t booleforce_current_bytes (void);
double booleforce_seconds (void);
void booleforce_print (FILE *);

/*------------------------------------------------------------------------*/

const char *booleforce_id (void);	/* CVS/RCS id */
const char *booleforce_version (void);
const char *booleforce_configuration (void);

/*------------------------------------------------------------------------*/
/* Internal functions that monitor entering and leaving the library.
 * Currently they are only used by the parser in 'bfapp.c' to add the
 * parse time to the overall time spent in the library.
 */
void booleforce_enter ();
void booleforce_leave ();

/*------------------------------------------------------------------------*/
#endif
