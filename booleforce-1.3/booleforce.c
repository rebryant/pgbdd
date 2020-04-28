/*------------------------------------------------------------------------*/
/* Copyright (c) 2005 - 2019 Armin Biere, Johannes Kepler University.     */
/*------------------------------------------------------------------------*/

#include "config.h"		/* include this first */

/*------------------------------------------------------------------------*/

#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <limits.h>

/*------------------------------------------------------------------------*/

#include "bfmem.h"
#include "bfstack.h"
#include "bfsort.h"
#include "bftime.h"
#include "bfio.h"
#include "bfnum.h"
#include "bftime.h"

/*------------------------------------------------------------------------*/

#include "booleforce.h"		/* include this last */

/*------------------------------------------------------------------------*/
#ifdef BOOLEFORCE_TRACE
/* This option is only useful if you want the generated traces to be easier
 * to read by humans.
 */
// #define SORT_ANTECEDENTS     /* sort antecedents by clause indices */
#endif
/*------------------------------------------------------------------------*/

#define USE_ZERO_PHASE_AS_DEFAULT

/*------------------------------------------------------------------------*/
/* NO COMPILE TIME CONFIGURATION NECESSARY BELOW THIS LINE */
/*------------------------------------------------------------------------*/

#define LD_RESCALE_VAR_INC -100
#define LD_RESCALE_CLAUSE_INC -100

/*------------------------------------------------------------------------*/

#define MAX_CLAUSE_IDX INT_MAX
#define MAX_VARIABLE_IDX INT_MAX
#define LD_MAX_CLAUSE_SIZE 20

/*------------------------------------------------------------------------*/
#ifdef BOOLEFORCE_STATS
#define ADD(s,delta) do { stats.s += (delta); } while (0)
#else
#define ADD(s,delta) do { } while (0)
#endif
/*------------------------------------------------------------------------*/

#define INC(s) ADD(s,1)

/*------------------------------------------------------------------------*/

#define MAX(a,b) ((a) < (b) ? (b) : (a))

/*------------------------------------------------------------------------*/

#define PERCENT(part,all) \
 (100.0 * (((all) > 0) ? (part) / (double)(all) : 0.0))

/*------------------------------------------------------------------------*/

#define AVG(s,n) \
  (((n) > 0) ? (s) / (double) (n) : 0.0)

/*------------------------------------------------------------------------*/

typedef struct Var Var;
typedef struct Lit Lit;
typedef struct Clause Clause;
typedef struct ClauseStats ClauseStats;
typedef struct DynamicClauseStats DynamicClauseStats;
typedef struct Stats Stats;
typedef struct Limits Limits;
typedef struct Frame Frame;
typedef struct Interval Interval;

/*------------------------------------------------------------------------*/

DeclarePtrStack (Clause);
DeclareStack (Frame);
DeclarePtrStack (Frame);

/*------------------------------------------------------------------------*/

enum Result
{
  FALSE = -1,
  UNKNOWN = 0,
  TRUE = 1,
};

typedef enum Result Result;

/*------------------------------------------------------------------------*/

struct Lit
{
  intStack watch2;		/* watched clauses by this literal */
  unsigned tla;			/* top level assignments when last checked */
};

/*------------------------------------------------------------------------*/

struct Var
{
  int level;
  int mark;
  int pos;
  BfUwe score;
  Clause *reason;
  unsigned top_level_assigned;
  unsigned initialized:1;
  unsigned core:1;
};

/*------------------------------------------------------------------------*/

struct Clause
{
  unsigned idx;
  BfUwe score;
  unsigned size : LD_MAX_CLAUSE_SIZE;

  /* The following three flags are actually one hot encoded.
   */
  unsigned original:1;
  unsigned learned:1;
  unsigned resolved:1;

  unsigned reason:1;		/* active as reason */
  unsigned dying:1;		/* on dying stack */
#ifndef NDEBUG
  unsigned connected:1;
  unsigned mark:1;
#endif
#ifdef BOOLEFORCE_TRACE
  unsigned core:1;
  unsigned antecedents:1;
#endif
  int cells[1];
};

/*------------------------------------------------------------------------*/

struct Interval
{
  int start;
  int last;
};

/*------------------------------------------------------------------------*/

struct Frame
{
  unsigned mark;
  Interval trail;	/* on 'trail' stack */
  Interval premisses;	/* on 'resolved_premisses' stack */
};

/*------------------------------------------------------------------------*/

struct ClauseStats
{
  int clauses;
  int64 literals;
#ifdef BOOLEFORCE_STATS
  int unary;
  int binary;
  int large;
#endif
};

/*------------------------------------------------------------------------*/

struct DynamicClauseStats
{
  ClauseStats added;
  ClauseStats removed;
  ClauseStats current;
  ClauseStats max;
};

/*------------------------------------------------------------------------*/

struct Stats
{
  int variables;

  DynamicClauseStats original;
  DynamicClauseStats resolved;
  DynamicClauseStats learned;
  DynamicClauseStats all;

  int progress_reports;
  double seconds;
  int64 conflicts;
  int decisions;
  int iterations;
  int gcs;
  int64 recycled_literals;
  int64 recycled_clauses;
#ifdef BOOLEFORCE_STATS
  int full_top_level_gcs;
  int fast_top_level_gcs;
  int reduce_learned_clauses_gcs;
  int64 reduced_learned_clauses;
  int64 reduced_learned_literals;
  int64 recycled_bytes;
  double gc_time;

  int restarts;
  int variable_rescales;
  int clause_rescales;

  int small_decision_clauses;
  int small_decision_clauses_sum;
  int uips;

  int64 resolved_premisses;
  int64 resolved_implications;
  int64 resolved_implication_chains;

  int64 unshrunken_literals;
  int64 shrunken_literals;
  int64 shrunken_clauses;

  int trivial_clauses;

  int failed_literals;
  int assignments_through_failed_literals;
  int failed_literal_rounds;
  int64 sum_height_at_conflict;
  int64 sum_conflict_frame_range;
  int64 sum_conflict_frames;
  int64 analyzed_frames;
  int64 backtracks;
  int64 backjumps;
  int64 backjumpedlevels;
  int assume_decisions;
  int random_decisions;
  int score_decisions;
  int64 pushs;
  int64 pops;
  int64 antecedents;
  int64 propagations;
  int64 bcps;
  int64 assignments;
  int64 visits;
  int64 traversals;
  int64 other_watched_true;
  int64 var_score_incs;
  int64 clause_score_incs;
  int64 swaps;
  int64 swaps_per_var_score_inc;
  int64 swaps_per_push;
  int64 swaps_per_pop;
#endif
};

/*------------------------------------------------------------------------*/

struct Limits
{
  int conflicts;
  int decisions;
  double time;
};

/*------------------------------------------------------------------------*/

enum State
{
  RESET_STATE = 0,
  INITIALIZED_STATE = 1,
};

typedef enum State State;

/*------------------------------------------------------------------------*/

static State state;

/*------------------------------------------------------------------------*/

static FILE *output;
static const char * output_name;
static int verbose;

#ifndef NDEBUG
static int check;
#endif
#ifdef BOOLEFORCE_TRACE
static int trace;
static int vars_core_generated;
static int clausal_core_generated;
#endif

/*------------------------------------------------------------------------*/

static int max_variable_idx;
static int size_variables;
static Lit *literals;
static Var *variables;
static signed char *assignment;

/*------------------------------------------------------------------------*/

static intStack resolved_literals;
static intStack resolved_premisses;
static intStack resolved_clauses;

static ClausePtrStack clauses;
static ClausePtrStack dying_clauses;
static intStack unit_clauses;
static Clause *empty_clause;

#ifdef BOOLEFORCE_TRACE
static intStack idx2antecedents;
static intStack antecedents;
#endif

static intStack sort_stack;
static intStack reduce_learned_clauses_stack;
static intStack dfs_stack;

/*------------------------------------------------------------------------*/

static int small_decision_clause_size;

static int disable_resolution_of_implication_chains;
static int disable_resolution_of_non_binary_implication_chains;
static int disable_recursive_resolution_of_literals;
static int disable_trimming_of_implication_chains;
static int disable_all_shrinking;
static int disable_failed_literals;
static int disable_first_uip;

/*------------------------------------------------------------------------*/

static int level;
static FrameStack control;
static intStack trail;
static int next_propagation;

static Clause *conflict;
static FramePtrStack frames;
static int uip;

/*------------------------------------------------------------------------*/

static unsigned assigned;
static unsigned unassigned;
static unsigned top_level_assigned;	/* abbrv: 'tla' */
static unsigned tla_full_gc;		/* tla at last full top level gc */
static unsigned tla_fast_gc;		/* tla at last fast top level gc */
static intStack ranking;
static intStack assumptions;

/*------------------------------------------------------------------------*/

static int disable_inc_score;
static BfUwe var_score_inc;
static BfUwe clause_score_inc;

/*------------------------------------------------------------------------*/

static unsigned rng_state;
static unsigned rng_seed;

/*------------------------------------------------------------------------*/

static int64 conflicts_limit_for_restart;
static int conflicts_limit_inc_for_restart;
static int conflicts_limit_inc_inc_rate_for_restart;	/* in percent */

/*------------------------------------------------------------------------*/

static int learned_limit_for_reduce;

/*------------------------------------------------------------------------*/

static int flushed_report;

/*------------------------------------------------------------------------*/

static Stats stats;
static Limits limits;

/*------------------------------------------------------------------------*/

static double entered_time;
static int entered;

/*------------------------------------------------------------------------*/
/* This is a random number generator from 'Numerical Recipes in C'.
 */
static unsigned
rng (void)
{
  unsigned res = rng_state;
  rng_state *= 1664525;
  rng_state += 1013904223;
#ifdef BOOLEFORCE_LOG
  if (verbose >= 6)
    fprintf (output, "c rng %u\n", res);
#endif
  return res;
}

/*------------------------------------------------------------------------*/

static unsigned
rng_one_out_of_two_to_the_power (int exponent)
{
  unsigned res;

  res = rng ();
  if (exponent < 32)
    res >>= (32 - exponent) / 2;

  res &= (1 << exponent) - 1;

  return res;
}

/*------------------------------------------------------------------------*/

static size_t
bytes_literals (int n)
{
  return sizeof (literals[0]) * 2 * n;
}

/*------------------------------------------------------------------------*/

static size_t
bytes_variables (int n)
{
  return n ? sizeof (variables[0]) * (n + 1) : 0;
}

/*------------------------------------------------------------------------*/

static void
check_legal_lit_idx (int idx)
{
  (void) idx;
  assert (-max_variable_idx <= idx);
  assert (idx);
  assert (idx <= max_variable_idx);
}

/*------------------------------------------------------------------------*/

static int
idx2unsigned (int idx)
{
  int res;
  res = (idx < 0) ? -idx : idx;
  return res;
}

/*------------------------------------------------------------------------*/

static Lit *
idx2lit (int idx)
{
  Lit *res;

  check_legal_lit_idx (idx);
  res = literals + 2 * idx2unsigned (idx) + (idx < 0);

  return res;
}

/*------------------------------------------------------------------------*/

static Var *
idx2var (int idx)
{
  return variables + idx2unsigned (idx);
}

/*------------------------------------------------------------------------*/

static int
idx2level (int idx)
{
  return idx2var (idx)->level;
}

/*------------------------------------------------------------------------*/

static int
idx2sign (int idx)
{
  int res;
  res = (idx < 0) ? -1 : 1;
  return res;
}

/*------------------------------------------------------------------------*/

static int *
end_of_cells (Clause * clause)
{
  return clause->cells + clause->size;
}

/*------------------------------------------------------------------------*/
#if defined(BOOLEFORCE_TRACE) || defined(BOOLEFORCE_LOG)
/*------------------------------------------------------------------------*/

static void
print_clause_with_white_space (Clause * clause, FILE * file)
{
  int *p, *eoc = end_of_cells (clause);

  for (p = clause->cells; p < eoc; p++)
    fprintf (file, " %d", *p);
}

/*------------------------------------------------------------------------*/
#endif
/*------------------------------------------------------------------------*/
#ifdef BOOLEFORCE_LOG
/*------------------------------------------------------------------------*/

static void
log_clause (Clause * clause)
{
  assert (clause->original + clause->learned + clause->resolved == 1);

  fputs ("c ", output);

  if (clause->original)
    fputs ("original", output);
  else if (clause->learned)
    fputs ("learned", output);
  else
    fputs ("resolved", output);

  fprintf (output, " clause %d:", clause->idx);
  print_clause_with_white_space (clause, output);
  fputc ('\n', output);
}

/*------------------------------------------------------------------------*/
#endif
/*------------------------------------------------------------------------*/

static void
mark_variables_in_resolved_literals (int new_mark)
{
  int *p;
  forall_stack (resolved_literals, p) idx2var (*p)->mark = new_mark;
}

/*------------------------------------------------------------------------*/

static int
is_trivial_resolved_literals (void)
{
  int res, *p, idx, mark;
  Var *var;

  res = 0;

  forall_stack (resolved_literals, p)
  {
    idx = *p;
    var = idx2var (idx);
    mark = idx2sign (idx);
    if (var->mark == -mark)
      res = 1;
    var->mark = mark;
  }

  mark_variables_in_resolved_literals (0);

  if (res)
    {
      INC (trivial_clauses);
#ifdef BOOLEFORCE_LOG
      if (verbose >= 4)
	{
	  fprintf (output, "c ignoring trivial clause:");
	  forall_stack (resolved_literals, p) fprintf (output, " %d", *p);
	  fputc ('\n', output);
	}
#endif
    }

  return res;
}

/*------------------------------------------------------------------------*/

static size_t
bytes_clause (int size)
{
  size_t res;

  assert (size >= 0);
  res = (size_t) (void *) &(((Clause *) 0)->cells);
  res += sizeof (((Clause *) 0)->cells[0]) * size;

  return res;
}

/*------------------------------------------------------------------------*/

#define ADD_CLAUSE_STAT(cs,member,inc) \
  do { \
    cs->current.member += inc; \
    assert (cs->current.member >= 0); \
    if (inc >= 0) \
      { \
	cs->added.member += inc; \
	if (cs->max.member < cs->current.member) \
	  cs->max.member = cs->current.member; \
	assert (cs->max.member >= 0); \
      } \
    else \
      { \
	cs->removed.member -= inc; \
      } \
  } while (0)

/*------------------------------------------------------------------------*/

static void
adjust_dynamic_clause_stats (DynamicClauseStats * cs, int size)
{
  int delta = (size < 0) ? -1 : 1;

  ADD_CLAUSE_STAT (cs, clauses, delta);
  ADD_CLAUSE_STAT (cs, literals, size);
#ifdef BOOLEFORCE_STATS
  if (size < 0)
    size = -size;

  if (size == 1)
    ADD_CLAUSE_STAT (cs, unary, delta);
  else if (size == 2)
    ADD_CLAUSE_STAT (cs, binary, delta);
  else if (size)
    ADD_CLAUSE_STAT (cs, large, delta);
#endif
}

/*------------------------------------------------------------------------*/

static void
adjust_clause_stats (Clause * clause, int delta)
{
  if (clause->original)
    {
      adjust_dynamic_clause_stats (&stats.original, delta);
    }
  else if (clause->learned)
    {
      adjust_dynamic_clause_stats (&stats.learned, delta);
    }
  else
    {
      assert (clause->resolved);
      adjust_dynamic_clause_stats (&stats.resolved, delta);
    }

  adjust_dynamic_clause_stats (&stats.all, delta);
}

/*------------------------------------------------------------------------*/

static void
check_legal_clause_idx (int idx)
{
  (void) idx;
  assert (0 < idx);
  assert (idx < count_stack (clauses));
}

/*------------------------------------------------------------------------*/

static Clause *
idx2clause (int idx)
{
  Clause *res;
  int abs_idx;

  abs_idx = (idx < 0) ? -idx : idx;
  check_legal_clause_idx (abs_idx);
  res = clauses.start[abs_idx];
  assert (res);

  return res;
}

/*------------------------------------------------------------------------*/

static Clause *
alloc_clause (int original, int learned)
{
  int size = count_stack (resolved_literals);
  size_t bytes;
  Clause *res;

  if (size >= (1 << LD_MAX_CLAUSE_SIZE))
    {
      fprintf (stderr, 
	       "libbooleforce: clause length (1 << %d) violated\n",
	       LD_MAX_CLAUSE_SIZE);
      abort ();
    }

  ADD (antecedents, count_stack (resolved_clauses));

  bytes = bytes_clause (size);
  res = booleforce_new (bytes);
  res->size = size;

  if (original)
    {
      assert (!learned);
      res->original = 1;
    }
  else
    {
      assert (!res->original);
      res->learned = (learned != 0);
      res->resolved = (learned == 0);
    }

  /* We want to use a zero clause index as sentinel, or to denote a
   * decision.  Therefore we need to add a dummy clause with index 0.
   */
  if (!count_stack (clauses))
    {
      push_stack (clauses, 0);			/* no clause */
#ifdef BOOLEFORCE_TRACE
      if (trace)
	push_stack (antecedents, INT_MAX);	/* illegal */
#endif
    }

  res->idx = count_stack (clauses);

  assert (res->idx > 0);
  assert (res->idx <= MAX_CLAUSE_IDX);

  push_stack (clauses, res);
  assert (idx2clause (res->idx) == res);

  adjust_clause_stats (res, res->size);

  return res;
}

/*------------------------------------------------------------------------*/

static void
connect_empty_clause (Clause * clause)
{
  assert (!clause->size);
  if (empty_clause)
    return;

  empty_clause = clause;
#ifdef BOOLEFORCE_LOG
  if (verbose >= 3)
    fprintf (output, "c connecting empty clause %d\n", clause->idx);
#endif
}

/*------------------------------------------------------------------------*/

static void
connect_unit_clause (Clause * clause)
{
  assert (clause->size == 1);
  push_stack (unit_clauses, clause->idx);
#ifdef BOOLEFORCE_LOG
  if (verbose >= 4)
    fprintf (output, "c connecting unit clause %d\n", clause->idx);
#endif
}

/*------------------------------------------------------------------------*/

static int
cmp_int (int a, int b)
{
  return a - b;
}

/*------------------------------------------------------------------------*/

static int
deref_idx (int idx)
{
  check_legal_lit_idx (idx);
  return idx2sign (idx) * assignment[idx2unsigned (idx)];
}

/*------------------------------------------------------------------------*/

static int
cmp_watched (int a, int b)
{
  int a_level, b_level, u, v, res;

  assert (a != b);

  u = deref_idx (a);
  v = deref_idx (b);

  if (u == TRUE && v != TRUE)
    return 1;

  if (u != TRUE && v == TRUE)
    return -1;

  if (u == FALSE && v != FALSE)
    return -1;

  if (u != FALSE && v == FALSE)
    return 1;

  a_level = idx2level (a);
  b_level = idx2level (b);

  res = cmp_int (a_level, b_level);

  if (u == TRUE && v == TRUE)
    {
      if (res)
	return -res;		/* smaller level is better */
    }
  else
    {
      if (res)
	return res;		/* larger level is better */
    }

  assert (u == v);

  if (a < 0)
    a = -a;

  if (b < 0)
    b = -b;

  res = -cmp_int (a, b);

  return res;
}

/*------------------------------------------------------------------------*/

static void
swap_int (int *a, int *b)
{
  int tmp = *a;
  *a = *b;
  *b = tmp;
}

/*------------------------------------------------------------------------*/

static int *
find_watched (Clause * clause, int *except)
{
  int *res, *p, *eoc = end_of_cells (clause);

  res = 0;

  for (p = clause->cells; p < eoc; p++)
    {
      if (p == except)
	continue;

      if (res && cmp_watched (*p, *res) < 0)
	continue;

      res = p;
    }

  assert (res);

  return res;
}

/*------------------------------------------------------------------------*/

static void
check_legal_ranking_pos (int pos)
{
#ifndef NDEBUG
  int count = count_stack (ranking);
  assert (pos >= 0);
  assert (pos < count);
#endif
  (void) pos;
}

/*------------------------------------------------------------------------*/

static int
parent_in_ranking (int pos)
{
  assert (0 < pos);
  check_legal_ranking_pos (pos);
  return pos / 2;
}

/*------------------------------------------------------------------------*/

static int
left_child_in_ranking (int pos)
{
  check_legal_ranking_pos (pos);
  return 2 * pos;
}

/*------------------------------------------------------------------------*/

static int
right_child_in_ranking (int pos)
{
  check_legal_ranking_pos (pos);
  return 2 * pos + 1;
}

/*------------------------------------------------------------------------*/

static int
pos2idx (int pos)
{
  check_legal_ranking_pos (pos);
  return ranking.start[pos];
}

/*------------------------------------------------------------------------*/

static int
cmp_ranking (int p, int q)
{
  int i, j;
  BfUwe s, t;

  i = pos2idx (p);
  j = pos2idx (q);

  check_legal_lit_idx (i);
  check_legal_lit_idx (j);

  s = idx2var (i)->score;
  t = idx2var (j)->score;

  return booleforce_cmp_uwe (s, t);
}

/*------------------------------------------------------------------------*/
#ifdef BOOLEFORCE_LOG
/*------------------------------------------------------------------------*/

static void
log_var_moved (int idx, int from, int to)
{
  fprintf (output,
           "c moved variable %d %s from position %d to %d\n", 
	   idx,
	   (from < to) ? "down" : "up",
	   from, to);
}

/*------------------------------------------------------------------------*/
#endif
/*------------------------------------------------------------------------*/

static void
swap_ranking (int p, int q)
{
#ifdef BOOLEFORCE_LOG
  int old_u_pos, old_v_pos;
#endif
  Var *u, *v;
  int i, j;

  INC (swaps);

  i = pos2idx (p);
  j = pos2idx (q);

  u = idx2var (i);
  v = idx2var (j);

#ifdef BOOLEFORCE_LOG
  old_u_pos = u->pos;
  old_v_pos = v->pos;
#endif
  u->pos = q;
  v->pos = p;

  ranking.start[p] = j;
  ranking.start[q] = i;
#ifdef BOOLEFORCE_LOG
  if (verbose >= 6)
    {
      log_var_moved (i, old_u_pos, u->pos);
      log_var_moved (j, old_v_pos, v->pos);
    }
#endif
}

/*------------------------------------------------------------------------*/

static int
up_ranking (int this)
{
  int parent;

  while (this > 0)
    {
      parent = parent_in_ranking (this);
      if (cmp_ranking (parent, this) >= 0)
	break;

      swap_ranking (this, parent);
      this = parent;
    }

  return this;
}

/*------------------------------------------------------------------------*/

static void
connect_large_clause (Clause * clause)
{
  int *tmp, *p0, *p1, i0, i1, clause_idx;
  Lit *l0, *l1;

  assert (clause->size >= 1);

  tmp = find_watched (clause, 0);
  p0 = clause->cells + 0;
  swap_int (tmp, p0);

  tmp = find_watched (clause, p0);
  p1 = clause->cells + 1;
  swap_int (tmp, p1);

  i0 = *p0;
  i1 = *p1;

  l0 = idx2lit (i0);
  l1 = idx2lit (i1);

  clause_idx = clause->idx;

  if (clause->size == 2)
    clause_idx = -clause_idx;

  push_stack (l0->watch2, clause_idx);
  push_stack (l1->watch2, clause_idx);

  if (clause->size == 2)
    {
      push_stack (l0->watch2, i1);
      push_stack (l1->watch2, i0);
    }

#ifdef BOOLEFORCE_LOG
  if (verbose >= 4)
    fprintf (output, "c connecting large clause %d\n", clause->idx);

  if (verbose >= 5)
    fprintf (output, "c watching %d and %d in clause %d\n",
	     i0, i1, clause->idx);
#endif
}

/*------------------------------------------------------------------------*/

static int
clause_unsatisfied (Clause * clause)
{
  int *p, *eoc = end_of_cells (clause);
  for (p = clause->cells; p < eoc; p++)
    if (deref_idx (*p) != FALSE)
      return 0;

  return 1;
}

/*------------------------------------------------------------------------*/

static int
forced_literal (Clause * clause)
{
  int *p, *eoc = end_of_cells (clause), idx, tmp;

  idx = 0;
  for (p = clause->cells; p < eoc; p++)
    {
      tmp = deref_idx (*p);

      if (tmp == TRUE)
	return 0;

      if (tmp == FALSE)
	continue;

      if (tmp == UNKNOWN)
	{
	  if (idx)
	    return 0;

	  idx = *p;
	}
    }

  return idx;
}

/*------------------------------------------------------------------------*/
#ifndef NDEBUG
/*------------------------------------------------------------------------*/

static int
clause_is_watched2 (Clause * clause, int idx)
{
  Lit *lit = idx2lit (idx);
  int *p, *eow = lit->watch2.last;
  int clause_idx = clause->idx;

  if (clause->size == 2)
    clause_idx = -clause_idx;

  for (p = lit->watch2.start; p < eow; p++)
    {
      if (*p == clause_idx)
	return 1;

      if (*p < 0)
	p++;
    }

  return 0;
}

/*------------------------------------------------------------------------*/

static void
check_clause_properly_connected (Clause * clause)
{
  int *p, *eoc, idx, tmp, tmp1, tmp2, num_unknown, num_true, num_false;

  assert (check > 0);

  if (clause->size < 2)
    return;

  num_unknown = num_true = num_false = 0;
  eoc = end_of_cells (clause);

  for (p = clause->cells; p < eoc; p++)
    {
      idx = *p;
      tmp = deref_idx (idx);

      if (tmp == UNKNOWN)
	num_unknown++;

      if (tmp == FALSE)
	num_false++;

      if (tmp == TRUE)
	num_true++;
    }

  assert (num_true + num_false + num_unknown == clause->size);

  tmp1 = deref_idx (clause->cells[0]);
  tmp2 = deref_idx (clause->cells[1]);

  if (tmp1 != TRUE && tmp2 != TRUE)
    {
      if (num_unknown == 1)
	assert (tmp1 == UNKNOWN || tmp2 == UNKNOWN);

      if (num_unknown > 1)
	assert (tmp1 == UNKNOWN && tmp2 == UNKNOWN);
    }

  if (check < 2)
    return;

  assert (clause->connected == clause_is_watched2 (clause, clause->cells[0]));
  assert (clause->connected == clause_is_watched2 (clause, clause->cells[1]));

  if (check < 3)
    return;

  for (p = clause->cells + 2; p < eoc; p++)
    assert (!clause_is_watched2 (clause, *p));
}

/*------------------------------------------------------------------------*/

static void
check_watch_list_correct (int idx)
{
  int *p, *eow, clause_idx;
  Clause *clause;
  Lit *lit;

  if (!idx)
    return;

  lit = idx2lit (idx);
  eow = lit->watch2.last;

  for (p = lit->watch2.start; p < eow; p++)
    {
      clause_idx = *p;
      if (!clause_idx)
	continue;

      clause = idx2clause (clause_idx);
      assert (clause->cells[0] == idx || clause->cells[1] == idx);
      if (clause_idx < 0)
	{
	  int other_idx;

	  assert (clause->size == 2);
	  p++;
	  assert (p < eow);
	  other_idx = *p;
	  if (clause->cells[0] == idx)
	    assert (clause->cells[1] == other_idx);
	  else
	    assert (clause->cells[0] == other_idx);
	}
    }
}

/*------------------------------------------------------------------------*/

static void
check_all_watch_list_correct (void)
{
  int i;

  for (i = -max_variable_idx; i <= max_variable_idx; i++)
    check_watch_list_correct (i);
}

/*------------------------------------------------------------------------*/

static void
check_no_clause_unsatisfied (void)
{
  Clause **p, * clause;

  for (p = clauses.start; p < clauses.last; p++)
    {
      clause = *p;

      if (!clause)
	continue;

      if (clause->dying)
	continue;

      assert (!clause_unsatisfied (clause));
    }
}

/*------------------------------------------------------------------------*/

static int
clause_satisfied (Clause * clause)
{
  int *p, *eoc = end_of_cells (clause);
  for (p = clause->cells; p < eoc; p++)
    if (deref_idx (*p) == TRUE)
      return 1;

  return 0;
}

/*------------------------------------------------------------------------*/

static void
check_all_clauses_satisfied (void)
{
  Clause **p, * clause;

  for (p = clauses.start; p < clauses.last; p++)
    {
      clause = *p;
      if (!clause)
	continue;

      /* it does not matter whether 'clause' is 'dying' or not.
       */
      assert (clause_satisfied (clause));
    }
}

/*------------------------------------------------------------------------*/

static void
check_current_clause_stats (void)
{
  int64 learned_literals = 0;
  int64 original_literals = 0;
  int64 resolved_literals = 0;
  int64 all_literals = 0;
  int learned_clauses = 0;
  int original_clauses = 0;
  int resolved_clauses = 0;
  int all_clauses = 0;

  Clause ** p, * clause;

  for (p = clauses.start; p < clauses.last; p++)
    {
      clause = *p;
      
      if (!clause)
	continue;

      if (clause->dying)
	continue;

      all_clauses++;
      all_literals += clause->size;

      if (clause->original)
	{
	  original_clauses++;
	  original_literals += clause->size;
	}
      else if (clause->learned)
	{
	  learned_clauses++;
	  learned_literals += clause->size;
	}
      else
	{
	  assert (clause->resolved);
	  resolved_clauses++;
	  resolved_literals += clause->size;
	}
    }

  assert (stats.all.current.clauses == all_clauses);
  assert (stats.all.current.literals == all_literals);

  assert (stats.learned.current.clauses == learned_clauses);
  assert (stats.learned.current.literals == learned_literals);

  assert (stats.original.current.clauses == original_clauses);
  assert (stats.original.current.literals == original_literals);

  assert (stats.resolved.current.clauses == resolved_clauses);
  assert (stats.resolved.current.literals == resolved_literals);
}

/*------------------------------------------------------------------------*/
#endif
/*------------------------------------------------------------------------*/

static void
connect_clause (Clause * clause)
{
  assert (!clause->connected);
  switch (clause->size)
    {
    case 0:
      connect_empty_clause (clause);
      break;

    case 1:
      connect_unit_clause (clause);
      break;

    default:
      connect_large_clause (clause);
      break;
    }

#ifndef NDEBUG
  clause->connected = 1;
  if (check)
    check_clause_properly_connected (clause);
#endif
}

/*------------------------------------------------------------------------*/

static int
new_size_variables (int idx)
{
  int res;

  assert (idx > 0);
  assert (idx > max_variable_idx);
  assert (idx >= size_variables);

  if (size_variables)
    res = 2 * size_variables;
  else
    res = 2;

  while (idx >= res)
    res *= 2;

  assert (idx < res);

  return res;
}

/*------------------------------------------------------------------------*/

static void
enlarge_literals (int new_size)
{
  size_t old_bytes = bytes_literals (size_variables);
  size_t new_bytes = bytes_literals (new_size);
  assert (old_bytes < new_bytes);
  literals = booleforce_enlarge (literals, old_bytes, new_bytes);
}

/*------------------------------------------------------------------------*/

static void
enlarge_assignment (int new_size)
{
  size_t old_bytes = size_variables;
  size_t new_bytes = new_size;
  assert (old_bytes < new_bytes);
  assignment = booleforce_enlarge (assignment, old_bytes, new_bytes);
}

/*------------------------------------------------------------------------*/

static void
enlarge_variables (int new_size)
{
  size_t old_bytes = bytes_variables (size_variables);
  size_t new_bytes = bytes_variables (new_size);
  assert (old_bytes < new_bytes);
  variables = booleforce_enlarge (variables, old_bytes, new_bytes);
}

/*------------------------------------------------------------------------*/

static void
push_ranking (int idx)
{
#ifdef BOOLEFORCE_STATS
  int64 old_swaps = stats.swaps;
#endif
  Var *var;
  int pos;

  assert (idx > 0);
  INC (pushs);
  pos = count_stack (ranking);
  var = idx2var (idx);
  var->pos = pos;
  push_stack (ranking, idx);
#ifdef BOOLEFORCE_LOG
  if (verbose >= 6)
    fprintf (output, "c added variable %d at position %d in ranking\n",
	     idx, var->pos);
#endif
  up_ranking (pos);
#ifdef BOOLEFORCE_STATS
  stats.swaps_per_push += stats.swaps - old_swaps;
#endif
}

/*------------------------------------------------------------------------*/

static void
down_ranking (int this)
{
  int other, child, count;

  count = count_stack (ranking);
  for (;;)
    {
      child = left_child_in_ranking (this);
      if (child >= count)
	break;

      other = right_child_in_ranking (this);

      if (cmp_ranking (this, child) < 0)
	{
	  if (other < count && cmp_ranking (child, other) < 0)
	    child = other;
	}
      else
	{
	  child = right_child_in_ranking (this);
	  if (child >= count || cmp_ranking (this, child) >= 0)
	    break;
	}

      swap_ranking (this, child);
      this = child;
    }
}

/*------------------------------------------------------------------------*/

static int
pop_ranking (int pos)
{
#ifdef BOOLEFORCE_STATS
  int64 old_swaps = stats.swaps;
#endif
  int count, last, res, tmp;
  Var *var;

  INC (pops);

  count = count_stack (ranking);

  assert (0 <= pos);
  assert (pos < count);

  last = count - 1;

  if (pos < last)
    swap_ranking (pos, last);

  res = pop_stack (ranking);

  if (pos < last)
    {
      tmp = up_ranking (pos);
      down_ranking (tmp);
#ifdef BOOLEFORCE_STATS
      stats.swaps_per_pop += stats.swaps - old_swaps;
#endif
    }

  var = idx2var (res);
  var->pos = -1;
#ifdef BOOLEFORCE_LOG
  if (verbose >= 6)
    fprintf (output, "c removed variable %d at rank %d\n", res, pos);
#endif

  return res;
}

/*------------------------------------------------------------------------*/

static void
rescale_variable_scores (void)
{
#ifdef BOOLEFORCE_LOG
  BfUwe old_var_score_inc = var_score_inc;
#endif
  BfUwe old_score, new_score;
  int idx;
  Var *v;

  INC (variable_rescales);
  assert (!booleforce_is_infinity_uwe (var_score_inc));
  var_score_inc = booleforce_shift_uwe (var_score_inc, LD_RESCALE_VAR_INC);
#ifdef BOOLEFORCE_LOG
  if (verbose >= 3)
    {
      fputs ("c rescaled variable score increment from ", output);
      booleforce_print_uwe (old_var_score_inc, output);
      fputs (" to ", output);
      booleforce_print_uwe (var_score_inc, output);
      fputc ('\n', output);
    }
#endif
  for (idx = 1; idx <= max_variable_idx; idx++)
    {
      v = idx2var (idx);
      if (!v->initialized)
	continue;

      old_score = v->score;
      new_score = booleforce_shift_uwe (old_score, LD_RESCALE_VAR_INC);
      v->score = new_score;
#ifdef BOOLEFORCE_LOG
      if (verbose >= 6)
	{
	  fprintf (output, "c rescaled score of variable %d from ", idx);
	  booleforce_print_uwe (old_score, output);
	  fputs (" to ", output);
	  booleforce_print_uwe (new_score, output);
	  fputc ('\n', output);
	}
#endif
    }
}

/*------------------------------------------------------------------------*/

static void
inc_var_score_inc (void)
{
#ifdef BOOLEFORCE_LOG
  BfUwe old_var_score_inc = var_score_inc;
#endif
  BfUwe new_var_score_inc, shifted;

  if (disable_inc_score)
    return;

  assert (!booleforce_is_zero_uwe (var_score_inc));
  assert (!booleforce_is_infinity_uwe (var_score_inc));

  shifted = booleforce_shift_uwe (var_score_inc, -4);
  new_var_score_inc = booleforce_add_uwe (var_score_inc, shifted);

  if (booleforce_is_infinity_uwe (new_var_score_inc))
    {
#ifdef BOOLEFORCE_LOG
      if (verbose >= 3)
	{
	  fputs ("c variable score increment ", output);
	  booleforce_print_uwe (var_score_inc, output);
	  fputs (" reached infinity\n", output);
	}
#endif
      rescale_variable_scores ();
    }
  else
    {
      var_score_inc = new_var_score_inc;
#ifdef BOOLEFORCE_LOG
      if (verbose >= 4)
	{
	  fputs ("c increased variable score increment from ", output);
	  booleforce_print_uwe (old_var_score_inc, output);
	  fputs (" to ", output);
	  booleforce_print_uwe (var_score_inc, output);
	  fputc ('\n', output);
	}
#endif
    }
}

/*------------------------------------------------------------------------*/

static void
inc_var_score_and_update_ranking (int idx)
{
  BfUwe old_score, new_score;
  Var *v;

  if (disable_inc_score)
    return;

  INC (var_score_incs);

  idx = idx2unsigned (idx);

  v = idx2var (idx);

  old_score = v->score;
  new_score = booleforce_add_uwe (old_score, var_score_inc);

  if (booleforce_is_infinity_uwe (new_score))
    {
#ifdef BOOLEFORCE_LOG
      if (verbose >= 3)
	{
	  fputs ("c score increment", output);
	  booleforce_print_uwe (old_score, output);
	  fputs (" + ", output);
	  booleforce_print_uwe (var_score_inc, output);
	  fputs (" = infinity\n", output);
	}
#endif
      rescale_variable_scores ();
      old_score = v->score;
      new_score = booleforce_add_uwe (old_score, var_score_inc);
    }

  v->score = new_score;

#ifdef BOOLEFORCE_LOG
  if (verbose >= 6)
    {
      fprintf (output, "c score of variable %d incremented from ", idx);
      booleforce_print_uwe (old_score, output);
      fputs (" to ", output);
      booleforce_print_uwe (new_score, output);
      fputc ('\n', output);
    }
#endif
  if (v->pos >= 0)
    {
#ifdef BOOLEFORCE_STATS
      int64 old_swaps = stats.swaps;
#endif
      up_ranking (v->pos);
#ifdef BOOLEFORCE_STATS
      stats.swaps_per_var_score_inc += stats.swaps - old_swaps;
#endif
    }
}

/*------------------------------------------------------------------------*/

static void
rescale_clause_scores (void)
{
  BfUwe old_score, new_score;
  Clause **p, *clause;
#ifdef BOOLEFORCE_LOG
  BfUwe old_clause_score_inc = clause_score_inc;
#endif
  INC (clause_rescales);

  clause_score_inc =
    booleforce_shift_uwe (clause_score_inc, LD_RESCALE_CLAUSE_INC);
#ifdef BOOLEFORCE_LOG
  if (verbose >= 3)
    {
      fputs ("c rescaled clause score increment from ", output);
      booleforce_print_uwe (old_clause_score_inc, output);
      fputs (" to ", output);
      booleforce_print_uwe (clause_score_inc, output);
      fputc ('\n', output);
    }
#endif
  for (p = clauses.start; p < clauses.last; p++)
    {
      clause = *p;

      if (!clause)
	continue;

      if (!clause->learned)
	continue;

      old_score = clause->score;
      new_score = booleforce_shift_uwe (old_score, LD_RESCALE_CLAUSE_INC);
      clause->score = new_score;
#ifdef BOOLEFORCE_LOG
      if (verbose >= 6)
	{
	  fprintf (output,
		   "c rescaled score of clause %d from ", clause->idx);
	  booleforce_print_uwe (old_score, output);
	  fputs (" to ", output);
	  booleforce_print_uwe (new_score, output);
	  fputc ('\n', output);
	}
#endif
    }
}

/*------------------------------------------------------------------------*/

static void
inc_clause_score (Clause * clause)
{
  BfUwe old_score, new_score;

  if (disable_inc_score)
    return;

  if (!clause->learned)
    return;

  INC (clause_score_incs);
  assert (!booleforce_is_zero_uwe (clause_score_inc));
  assert (!booleforce_is_infinity_uwe (clause_score_inc));

  old_score = clause->score;
  new_score = booleforce_add_uwe (old_score, clause_score_inc);

  if (booleforce_is_infinity_uwe (new_score))
    {
#ifdef BOOLEFORCE_LOG
      if (verbose >= 3)
	{
	  fputs ("c score increment ", output);
	  booleforce_print_uwe (old_score, output);
	  fputs (" + ", output);
	  booleforce_print_uwe (clause_score_inc, output);
	  fprintf (output, " for clause %d reached infinity\n", clause->idx);
	}
#endif
      rescale_clause_scores ();
      old_score = clause->score;
      new_score = booleforce_add_uwe (old_score, clause_score_inc);
    }

  clause->score = new_score;

#ifdef BOOLEFORCE_LOG
  if (verbose >= 6)
    {
      fprintf (output, "c score of clause %d incremented to ", clause->idx);
      booleforce_print_uwe (new_score, output);
      fputc ('\n', output);
    }
#endif
}

/*------------------------------------------------------------------------*/

static void
inc_clause_score_inc (void)
{
#ifdef BOOLEFORCE_LOG
  BfUwe old_clause_score_inc = clause_score_inc;
#endif
  BfUwe shifted, new_score_inc;

  if (disable_inc_score)
    return;

  shifted = booleforce_shift_uwe (clause_score_inc, -10);
  new_score_inc = booleforce_add_uwe (clause_score_inc, shifted);

  if (booleforce_is_infinity_uwe (new_score_inc))
    {
#ifdef BOOLEFORCE_LOG
      if (verbose >= 4)
	{
	  fputs ("c clause score increment ", output);
	  booleforce_print_uwe (clause_score_inc, output);
	  fputs (" reached infinity\n", output);
	}
#endif
      rescale_clause_scores ();
    }
  else
    {
      clause_score_inc = new_score_inc;
#ifdef BOOLEFORCE_LOG
      if (verbose >= 4)
	{
	  fputs ("c increased clause score increment from ", output);
	  booleforce_print_uwe (old_clause_score_inc, output);
	  fputs (" to ", output);
	  booleforce_print_uwe (new_score_inc, output);
	  fputc ('\n', output);
	}
#endif
    }
}

/*------------------------------------------------------------------------*/

static void
init_var (Var * var, int idx)
{
  assert (idx > 0);
  assert (!var->initialized);
  var->initialized = 1;
  var->pos = count_stack (ranking);
  push_stack (ranking, idx);
  stats.variables++;
  unassigned++;
  assert (unassigned);		/* check for wrap around */
}

/*------------------------------------------------------------------------*/

static void
uniq_resolved_literals (void)
{
  int *p, *q, idx;
  Var *v;

  q = p = resolved_literals.start;
  while (p < resolved_literals.last)
    {
      idx = *p++;
      v = idx2var (idx);
      if (v->mark)
	continue;
      v->mark = 1;
      *q++ = idx;
    }

  resolved_literals.last = q;
  while (q > resolved_literals.start)
    idx2var (*--q)->mark = 0;
}

/*------------------------------------------------------------------------*/

static void
copy_resolved_literals (Clause * clause)
{
  int idx, *p, *q, *eoc = end_of_cells (clause);

  p = resolved_literals.start;
  q = clause->cells;

  while (q < eoc)
    {
      idx = *p++;
      *q++ = idx;
    }

  reset_stack (resolved_literals, 0);
}

/*------------------------------------------------------------------------*/

static void
inc_resolved_clauses (void)
{
  int *p;

  for (p = resolved_clauses.start; p < resolved_clauses.last; p++)
    inc_clause_score (idx2clause (*p));
}

/*------------------------------------------------------------------------*/

static Clause *
add_original_clause (void)
{
  Clause *res;

  uniq_resolved_literals ();
  res = alloc_clause (1, 0);
  copy_resolved_literals (res);
#ifdef BOOLEFORCE_LOG
  if (verbose >= 4)
    log_clause (res);
#endif
  connect_clause (res);
  inc_clause_score (res);

  return res;
}

/*------------------------------------------------------------------------*/

static void
unassign (int idx)
{
  Clause *reason;
  Var *var;

  var = idx2var (idx);

  assert (var->level <= level);
  assert (deref_idx (idx) != UNKNOWN);
  assert (deref_idx (-idx) == -deref_idx (idx));

  reason = var->reason;
  if (reason)
    {
      assert (reason->reason);
      reason->reason = 0;
    }

  assignment[idx2unsigned (idx)] = UNKNOWN;

  if (var->pos < 0)
    push_ranking (idx2unsigned (idx));

  unassigned++;
  assert (unassigned);		/* check for wrap around */

  assert (assigned);
  assigned--;

#ifdef BOOLEFORCE_LOG
  if (verbose >= 4)
    fprintf (output, "c unassigned %d at level %d\n",
	     idx, idx2var (idx)->level);
#endif
}

/*------------------------------------------------------------------------*/

static void
reset_control (int new_level)
{
  Frame * frame;

  level = new_level;

  frame = control.start + level;
  control.last = frame + 1;
  frame->trail.last = -1;		/* mark it as undefined again */
#ifdef BOOLEFORCE_LOG
  if (verbose >= 5)
    fprintf (output, 
	     "c reopening frame at level %d with trail [%d,%d[\n",
	     level, frame->trail.start, count_stack (trail));
#endif
}

/*------------------------------------------------------------------------*/

static void
undo (int new_level)
{
#if defined(BOOLEFORCE_STATS) || defined(BOOLEFORCE_LOG)
  int jumps = level - new_level - 1;
#endif
  int idx;

  assert (new_level < level);

#ifdef BOOLEFORCE_STATS
  if (jumps > 0)
    {
      INC (backjumps);
      ADD (backjumpedlevels, jumps);
    }
#endif
#ifdef BOOLEFORCE_LOG
  if (verbose >= 4)
    {
      if (jumps > 0)
	fprintf (output, "c backjumping %d levels\n", jumps);

      fprintf (output, "c backtracking to level %d\n", new_level);

      if (new_level + 1 == level)
	fprintf (output, "c unassigning variables on level %d\n", level);
      else
	fprintf (output,
		 "c unassigning variables on levels %d to %d\n",
		 new_level + 1, level);
    }
#endif
  conflict = 0;
  uip = 0;
  if (new_level < 0)
    new_level = 0;

  while (trail.last > trail.start)
    {
      idx = trail.last[-1];
      if (new_level == idx2level (idx))
	break;

      trail.last--;
      unassign (idx);
    }

  reset_control (new_level);
  next_propagation = count_stack (trail);
}

/*------------------------------------------------------------------------*/
/* Determine the second largest level, which is the level to which we
 * backtrack in order to make the clause satisfiable, assuming that it is
 * unsatisfied before backtracking.
 */
static int
determine_backtrack_level (Clause * clause)
{
  int *p, *eoc = end_of_cells (clause), idx, res, max, tmp;

  assert (clause_unsatisfied (clause));

  max = 0;
  for (p = clause->cells; p < eoc; p++)
    {
      idx = *p;
      assert (deref_idx (idx) == FALSE);
      tmp = idx2level (idx);
      if (tmp > max)
	max = tmp;
    }

  assert (max >= 0);

  res = -1;
  for (p = clause->cells; p < eoc; p++)
    if (res < (tmp = idx2level (*p)) && tmp < max)
      res = tmp;

  return res;
}

/*------------------------------------------------------------------------*/

static void
add_lit_as_int (int lit_as_int)
{
  int idx, new_size, new_level, other;
  Clause *clause;
  Var *var;

  idx = idx2unsigned (lit_as_int);

  assert (idx <= MAX_VARIABLE_IDX);

  if (idx)
    {
      if (idx >= size_variables)
	{
	  new_size = new_size_variables (idx);
	  assert (idx < new_size);

	  enlarge_literals (new_size);
	  enlarge_variables (new_size);
	  enlarge_assignment (new_size);

	  size_variables = new_size;
	}

      if (idx > max_variable_idx)
	max_variable_idx = idx;

      var = idx2var (idx);
      if (!var->initialized)
	init_var (var, idx);

      push_stack (resolved_literals, lit_as_int);
    }
  else
    {
      if (!is_trivial_resolved_literals ())
	{
	  clause = add_original_clause ();
	  if (clause->size == 0)
	    {
	      assert (empty_clause);
	    }
	  else
	    {
	      if (clause_unsatisfied (clause))
		{
#ifdef BOOLEFORCE_LOG
		  if (verbose >= 4)
		    fprintf (output,
			     "c original conflicting clause %d\n",
			     clause->idx);
#endif
		  new_level = determine_backtrack_level (clause);
		  if (new_level != level)
		    undo (new_level);
		}

	      if ((other = forced_literal (clause)))
		{
#ifdef BOOLEFORCE_LOG
		  if (verbose >= 4)
		    fprintf (output,
			     "c original clause %d forcing %d\n",
			     clause->idx, other);
#endif
		}
	    }
	}

      reset_stack (resolved_literals, 0);
    }
}

/*------------------------------------------------------------------------*/

static void
reset_resolved_clauses (int count)
{
  int * start = resolved_clauses.start + count;
#ifndef NDEBUG
  int * last = resolved_clauses.last;
  Clause *clause;
  int idx, *p;

  for (p = start; p < last; p++)
    {
      idx = *p;
      clause = idx2clause (idx);
      clause->mark = 0;
    }
#endif
  resolved_clauses.last = start;
}

/*------------------------------------------------------------------------*/
#ifdef BOOLEFORCE_TRACE
/*------------------------------------------------------------------------*/

static int *
clause2antecedents (Clause * clause)
{
  int pos, * res;

  assert (clause->antecedents);
  assert (clause->idx < (unsigned) count_stack (idx2antecedents));

  pos = idx2antecedents.start[clause->idx];
  res = pos ? antecedents.start + pos : 0;

  return res;
}

/*------------------------------------------------------------------------*/

static void
copy_antecedents (Clause * clause)
{
  int *p, pos, clause_idx, antecedent_idx;

  clause_idx = clause->idx;
  while (clause->idx >= (unsigned) count_stack (idx2antecedents))
    enlarge_stack (idx2antecedents);

  pos = count_stack (antecedents);
  assert (!idx2antecedents.start [clause_idx]);
  idx2antecedents.start[clause_idx] = pos;

  clause->antecedents = 1;
#ifdef SORT_ANTECEDENTS
  {
    int n = count_stack (resolved_clauses);
    booleforce_sort (int, cmp_int, resolved_clauses.start, n, sort_stack);
  }
#endif
  for (p = resolved_clauses.start; p < resolved_clauses.last; p++)
    {
      antecedent_idx = *p;
      push_stack (antecedents, antecedent_idx);
    }

  push_stack (antecedents, 0);
  assert (clause2antecedents (clause) == antecedents.start + pos);
}

/*------------------------------------------------------------------------*/
#endif
/*------------------------------------------------------------------------*/

static int
cmp_cell (int i, int j)
{
  int k = idx2level (i);
  int l = idx2level (j);
  int res = -cmp_int (k, l); /* higher level first */
  if (res)
    return res;

  return cmp_int (i, j);
}

/*------------------------------------------------------------------------*/

static void
sort_cells (Clause * clause)
{
  int size = clause->size, *cells = clause->cells;
  booleforce_sort (int, cmp_cell, cells, size, sort_stack);
}

/*------------------------------------------------------------------------*/

static Clause *
add_derived_clause (int learned)
{
  Clause *res;

  res = alloc_clause (0, learned);
  copy_resolved_literals (res);
  sort_cells (res);

#ifdef BOOLEFORCE_TRACE
  if (trace)
    copy_antecedents (res);
#endif
  if (learned)
    inc_resolved_clauses ();

  reset_resolved_clauses (0);

  assert (!res->original);
  assert (learned == res->learned);
#ifdef BOOLEFORCE_LOG
  if (verbose >= 4)
    log_clause (res);
#endif
  connect_clause (res);
  inc_clause_score (res);

  return res;
}

/*------------------------------------------------------------------------*/

static void
log_addition_of_resolved_literal (int idx)
{
  (void) idx;
#ifdef BOOLEFORCE_LOG
  if (verbose >= 5)
    fprintf (output,
	      "c adding resolved literal %d at level %d\n", idx, idx2level (idx));
#endif
}

/*------------------------------------------------------------------------*/

static void
add_resolved_literal (int idx)
{
  push_stack (resolved_literals, idx);
  log_addition_of_resolved_literal (idx);
}

/*------------------------------------------------------------------------*/
#ifdef BOOLEFORCE_LOG
/*------------------------------------------------------------------------*/

static void
log_resolved_clause (Clause * clause)
{
  int * p, * eoc = end_of_cells (clause);

  for (p = clause->cells; p < eoc; p++)
    if (deref_idx (*p) == TRUE)
      break;

  fprintf (output, "c resolving clause %d", clause->idx);

  if (p < eoc)
    fprintf (output, " on %d\n", *p);
  else
    fputs (" as initial resolvent\n", output);
}

/*------------------------------------------------------------------------*/
#endif
/*------------------------------------------------------------------------*/

static void
add_resolved_clause (Clause * clause)
{
#ifndef NDEBUG
  assert (!clause->mark);
  clause->mark = 1;
#endif
  push_stack (resolved_clauses, clause->idx);
#ifdef BOOLEFORCE_LOG
  if (verbose >= 6)
    log_resolved_clause (clause);
#endif
}

/*------------------------------------------------------------------------*/

static void
kill_clause (Clause * clause)
{
  assert (!clause->connected);
  assert (!clause->dying);
#ifdef BOOLEFORCE_LOG
  if (verbose >= 4)
    fprintf (output, "c killing clause %d\n", clause->idx);
#endif
  clause->dying = 1;
  push_stack (dying_clauses, clause);

  /* Already adjust clause stats now even if clause is not recycled yet.
   */
  adjust_clause_stats (clause, -clause->size);
}

/*------------------------------------------------------------------------*/

static void
remove_watch (int clause_idx, int idx)
{
  int *p, other_clause_idx;

  p = idx2lit(idx)->watch2.start;

  for (;;)
    {
      assert (p < idx2lit(idx)->watch2.last);
      other_clause_idx = *p++;

      if (other_clause_idx == clause_idx)
	{
	  p[-1] = 0;
	  if (other_clause_idx < 0)
	    p[0] = 0;

#ifdef BOOLEFORCE_LOG
	  if (verbose >= 4)
	    fprintf (output,
		     "c removed watch %d in clause %d\n",
		     idx, clause_idx);
#endif
	  break;
	}

      if (other_clause_idx < 0)
	p++;
    }
}

/*------------------------------------------------------------------------*/

static Clause *
resolve_top_level_reason (int idx, Clause * reason)
{
  int *p, *eoc = end_of_cells (reason), other_idx, tmp;
  Clause *res, *other_reason;
  Var *other_var;

  (void) idx;

  assert (!level);
  assert (reason);
  assert (reason->size > 1);
  assert (forced_literal (reason) == idx);
  assert (empty_stack (resolved_literals));
  assert (empty_stack (resolved_clauses));
  add_resolved_clause (reason);

  for (p = reason->cells; p < eoc; p++)
    {
      other_idx = *p;
      tmp = deref_idx (other_idx);

      if (tmp == UNKNOWN)
	{
	  assert (idx == other_idx);
	  add_resolved_literal (other_idx);
	}
      else
	{
	  assert (tmp == FALSE);
	  other_var = idx2var (other_idx);
	  other_reason = other_var->reason;
	  assert (other_reason);
	  assert (other_reason->size == 1);
	  add_resolved_clause (other_reason);
	}
    }

  res = add_derived_clause (0);

  return res;
}

/*------------------------------------------------------------------------*/

static void
assign (Clause * reason, int idx)
{
  Var *var;

  var = idx2var (idx);

  if (!level)
    {
      assert (reason);
      if (reason->size > 1)
	reason = resolve_top_level_reason (idx, reason);
    }

  INC (assignments);

  assignment[idx2unsigned (idx)] = idx2sign (idx);

  var->level = level;
  var->reason = reason;
  if (reason)
    {
      assert (!reason->reason);
      reason->reason = 1;
    }

  assert (unassigned > 0);
  unassigned--;

  assigned++;
  assert (assigned);

  if (!level)
    top_level_assigned++;

  push_stack (trail, idx);
#ifdef BOOLEFORCE_LOG
  if (verbose >= 4)
    {
      fprintf (output, "c assigned %d at level %d <= ", idx, level);
      if (reason)
	fprintf (output, "clause %d\n", reason->idx);
      else
	fputs ("decision\n", output);
    }
#endif
}

/*------------------------------------------------------------------------*/

static void
push_frame (void)
{
  Frame * frame;
  int count;

  count = count_stack (trail);
  if (level >= 0)
    {
      frame = control.last - 1;
      assert (control.start + level == frame);
      assert (frame->trail.last = -1);	/* still marked undefined */
      frame->trail.last = count;
#ifdef BOOLEFORCE_LOG
      if (verbose >= 5)
	fprintf (output, 
	         "c closing frame at level %d with trail [%d,%d[\n",
		 level, frame->trail.start, frame->trail.last);
#endif
    }
  else
    assert (!count);

  level++;

  if (full_stack (control))
    enlarge_stack (control);

  frame = control.last++;
  assert (control.last <= control.end);

  memset (frame, 0, sizeof (*frame));
  frame->trail.start = count;
  frame->trail.last = -1;			/* mark undefined */

#ifdef BOOLEFORCE_LOG
  if (verbose >= 5)
    fprintf (output, 
	     "c opening new frame at level %d with trail [%d,%d[\n",
	     level, frame->trail.start, frame->trail.start);
#endif
  assert (control.start + level == frame);
}
/*------------------------------------------------------------------------*/

static void
push_decision (int decision)
{
  stats.decisions++;
  push_frame ();
  assert (deref_idx (decision) == UNKNOWN);
#ifdef BOOLEFORCE_LOG
  if (verbose >= 4)
    fprintf (output, "c decision %d at level %d\n", decision, level);
#endif
  assign (0, decision);
}

/*------------------------------------------------------------------------*/

static void
push_conflict (Clause * clause)
{
  stats.conflicts++;
  ADD (sum_height_at_conflict, level);

  check_legal_clause_idx (clause->idx);

  assert (!conflict);
  conflict = clause;
}

/*------------------------------------------------------------------------*/
/* Fix the watched literals in the given clause.  Return a zero value
 * if the watched literal is still watched.  Otherwise return the index of
 * the newly watched literal.
 */
static int
find_new_watch (Clause * clause, int idx)
{
  int tmp, other, *cells, * p, * eoc;
  Lit * lit;

  assert (clause->size >= 2);

  INC (visits);
#ifdef BOOLEFORCE_LOG
  if (verbose >= 4)
    fprintf (output, "c visiting clause %d\n", clause->idx);
#endif
  if (clause->dying)
    return 0;

  cells = clause->cells;
  other = cells[0];
  if (other == -idx)
    {
      cells[0] = cells[1];
      cells[1] = -idx;
    }
  else
    assert (cells[1] == -idx);

  tmp = deref_idx (cells[0]);
  INC (traversals);

  if (tmp == TRUE)
    {
      INC (other_watched_true);
#ifdef BOOLEFORCE_LOG
      if (verbose >= 4)
	fprintf (output,
		 "c other watched literal %d in clause %d is TRUE\n",
		 cells[1], clause->idx);
#endif
      return 0;			/* keep old watch */
    }

  eoc = cells + clause->size;
  for (p = cells + 2; p < eoc; p++)
    {
      INC (traversals);

      other = *p;
      tmp = deref_idx (other);
      if (tmp != FALSE)
	{
	  *p = -idx;
	  cells[1] = other;
	  lit = idx2lit (other);
	  push_stack (lit->watch2, clause->idx);
#ifdef BOOLEFORCE_LOG
	  if (verbose >= 4)
	    fprintf (output,
		     "c literal %d assigned %s is watching clause %d\n",
		     other,
		     deref_idx (other) == TRUE ? "TRUE" : "UNKNOWN",
		     clause->idx);
#endif
	  return other;
	}
    }

  tmp = deref_idx (cells[0]);

  if (tmp == FALSE)
    {
#ifdef BOOLEFORCE_LOG
      if (verbose >= 4)
	fprintf (output,
		 "c all literals false in conflicting clause %d\n",
		 clause->idx);
#endif
      push_conflict (clause);
    }
  else
    {
      assert (tmp == UNKNOWN);
      assign (clause, cells[0]);
    }

  return 0;			/* keep old watch */
}

/*------------------------------------------------------------------------*/

inline static void
visit_binary_clause (Clause * clause, int other_literal)
{
  int tmp;

  assert (clause->size == 2);

  tmp = deref_idx (other_literal);

  if (tmp == TRUE)
    {
#ifdef BOOLEFORCE_LOG
      if (verbose >= 4)
	fprintf (output,
		 "c no visit to clause %d since other literal %d TRUE\n",
		 clause->idx, other_literal);
#endif
    }
  else if (tmp == FALSE)
    {
#ifdef BOOLEFORCE_LOG
      if (verbose >= 4)
	fprintf (output,
		 "c both watched literals "
		 "%d and %d in clause %d are FALSE\n",
		 clause->cells[0], clause->cells[1], clause->idx);
#endif
      push_conflict (clause);
    }
  else
    {
      assert (tmp == UNKNOWN);
      assign (clause, other_literal);
    }
}

/*------------------------------------------------------------------------*/

static void
propagate (int idx)
{
  int clause_idx, i, j, other;
  intStack * watches;
  Clause *clause;
  Lit *lit;

  INC (propagations);

  assert (deref_idx (idx) == TRUE);
  lit = idx2lit (-idx);
  watches = &lit->watch2;

  j = 0;
  for (i = 0; !conflict && i < count_stack (*watches); i++)
    {
      clause_idx = watches->start[i];
      if (!clause_idx)
	continue;		/* skip removed watches */

      clause = idx2clause (clause_idx);

      if (clause_idx < 0)
	{
          watches->start[j++] = watches->start[i++];
	  other = watches->start[i];
	  watches->start[j++] = other;

	  visit_binary_clause (clause, other);

	  continue;
	}

      if (find_new_watch (clause, idx))
	{
#ifdef BOOLEFORCE_LOG
	  if (verbose >= 4)
	    fprintf (output,
		     "c literal %d does not watch clause %d anymore\n",
		     idx, clause->idx);
#endif
	}
      else
	{
	  /* Keep old watch! However, we can not just use 'clause_idx' here
	   * since 'find_new_watch' can remove this watch through a call
	   * through 'assign' etc.  and 'remove_watch' on the top level.
	   */
	  watches->start[j++] = watches->start[i];
	}

#ifdef BOOLEFORCE_LOG
      if (verbose >= 4)
	fprintf (output,
		 "c watching literals %d and %d after visiting clause %d\n",
		 clause->cells[0], clause->cells[1], clause->idx);
#endif
    }

  /* After a conflict the references to the remaining non visited clauses
   * still need to be watched.
   */
  while (i < count_stack (*watches))
    watches->start[j++] = watches->start[i++];

  watches->last = watches->start + j;
#ifndef NDEBUG
  if (!conflict && check)
    {
      int * p;
      for (p = lit->watch2.start; p < lit->watch2.last; p++)
	{
	  clause_idx = *p;
	  if (!clause_idx)
	    continue;

	  check_clause_properly_connected (idx2clause (clause_idx));

	  if (clause_idx < 0)
	    p++;
	}
    }
#endif
}

/*------------------------------------------------------------------------*/

void
booleforce_enter (void)
{
  if (state != INITIALIZED_STATE)
    {
      fprintf (stderr, 
	       "libbooleforce: no initializing through 'booleforce_init'\n");
      abort ();
    }

  if (!entered++)
    entered_time = booleforce_time_stamp ();

  assert (entered > 0);		/* no overflow ? */
}

/*------------------------------------------------------------------------*/

static void
adjust_seconds (void)
{
  double current_time, delta;

  current_time = booleforce_time_stamp ();
  delta = current_time - entered_time;
  stats.seconds += ((delta >= 0) ? delta : 0.0);
  entered_time = current_time;
}

/*------------------------------------------------------------------------*/

static double
adjusted_seconds (void)
{
  if (entered)
    adjust_seconds ();
  return stats.seconds;
}

/*------------------------------------------------------------------------*/

void
booleforce_leave (void)
{
  assert (entered > 0);
  if (!--entered)
    adjust_seconds ();
}

/*------------------------------------------------------------------------*/

void
booleforce_add (int lit)
{
  booleforce_enter ();
  add_lit_as_int (lit);
  booleforce_leave ();
}

/*------------------------------------------------------------------------*/

static void
init_restart_limit (void)
{
  conflicts_limit_inc_for_restart = 100;
  conflicts_limit_inc_inc_rate_for_restart = 50;	/* 50% */

  conflicts_limit_for_restart = stats.conflicts;
  conflicts_limit_for_restart += conflicts_limit_inc_for_restart;
#ifdef BOOLEFORCE_LOG
  if (verbose >= 3)
    {
      fprintf (output,
	       "c initial restart limit increment %d\n",
	       conflicts_limit_inc_for_restart);

      fprintf (output,
        "c initial restart limit %" INT64FMT " at %"INT64FMT" conflicts\n",
	conflicts_limit_for_restart, stats.conflicts);

      fprintf (output,
	       "c restart limit increment increment rate %d%%\n",
	       conflicts_limit_inc_inc_rate_for_restart);
    }
#endif
}

/*------------------------------------------------------------------------*/

static void
inc_restart_limit (void)
{
  int64 incinc = 0;

  if (conflicts_limit_inc_inc_rate_for_restart > 0)
    {
      incinc = conflicts_limit_inc_for_restart;
      incinc *= conflicts_limit_inc_inc_rate_for_restart;
      incinc /= 100;
      conflicts_limit_inc_for_restart += incinc;
    }

  conflicts_limit_for_restart = stats.conflicts;
  conflicts_limit_for_restart += conflicts_limit_inc_for_restart;
#ifdef BOOLEFORCE_LOG
  if (verbose >= 3)
    {
      fprintf (output,
	       "c new restart limit increment %d incremented by %d\n",
	       conflicts_limit_inc_for_restart, (int) incinc);

      fprintf (output,
        "c new restart limit %" INT64FMT " at %"INT64FMT" conflicts\n",
	conflicts_limit_for_restart, stats.conflicts);
    }
#endif
}

/*------------------------------------------------------------------------*/

static void
init_reduce_limit (void)
{
  learned_limit_for_reduce = stats.all.current.clauses;
  learned_limit_for_reduce *= 2;
  learned_limit_for_reduce /= 3;

#ifdef BOOLEFORCE_LOG
  if (verbose >= 3)
    {
      fprintf (output,
	       "c initial reduce limit %d at %d clauses\n",
	       learned_limit_for_reduce, stats.all.current.clauses);
    }
#endif
}

/*------------------------------------------------------------------------*/

static void
inc_reduce_limit (int rate)
{
  int new_limit;

  if (rate > 0)
    {
      new_limit = learned_limit_for_reduce;
      new_limit *= 100 + rate;
      new_limit /= 100;
      learned_limit_for_reduce = new_limit;
    }

#ifdef BOOLEFORCE_LOG
  if (verbose >= 3)
    {
      fprintf (output,
	       "c new reduce limit %d at %d learned clauses\n",
	       learned_limit_for_reduce, stats.learned.current.clauses);
    }
#endif
}

/*------------------------------------------------------------------------*/

static double
max_mega_bytes (void)
{
  return booleforce_max_bytes () / (double) (1 << 20);
}

/*------------------------------------------------------------------------*/

static double
current_mega_bytes (void)
{
  return booleforce_current_bytes () / (double) (1 << 20);
}

/*------------------------------------------------------------------------*/
#ifdef BOOLEFORCE_STATS
/*------------------------------------------------------------------------*/

static double
avg_height (void)
{
  return AVG (stats.sum_height_at_conflict, stats.conflicts);
}

/*------------------------------------------------------------------------*/

static double
avg_range (void)
{
  return AVG (stats.sum_conflict_frame_range, stats.analyzed_frames);
}

/*------------------------------------------------------------------------*/

static double
avg_density (void)
{
  assert (stats.sum_conflict_frames <= stats.sum_conflict_frame_range);
  return PERCENT (stats.sum_conflict_frames, stats.sum_conflict_frame_range);
}

/*------------------------------------------------------------------------*/

static double
current_length (void)
{
  return AVG (stats.learned.current.literals, stats.learned.current.clauses);
}

/*------------------------------------------------------------------------*/
#endif
/*------------------------------------------------------------------------*/

static void
progress_report (char ch)
{
  if (!verbose)
    return;

  if (!stats.progress_reports++)
    {
#ifdef BOOLEFORCE_STATS
      fprintf (output,
	       "c\nc"
	       "               iterations"
	       "     conflicts"
	       "       length"
	       "      range"
	       "           tla"
	       "\n");
#endif
      fprintf (output,
	       "c"
	       "   seconds"
	        "    MB"
#ifdef BOOLEFORCE_STATS
	       "     decisions"
	       "         learned"
	       "      height"
	       "     density"
	       "\nc" 
#endif
	       "\n");
    }

  fprintf (output, "c %c", ch);
  fprintf (output, "%7.2f %6.1f"
#ifdef BOOLEFORCE_STATS
	   " %4d"
	     "%8d"
	   "%9" INT64FMT 
	     "%7d"
	   "%6.1f"
	     "%6.1f"
	   "%6.1f"
	     " %5.1f%%"
	   "%7d"
#endif
	   "\n", adjusted_seconds (), current_mega_bytes ()
#ifdef BOOLEFORCE_STATS
	   ,
	   stats.iterations, 
	     stats.decisions,
	   stats.conflicts,
	     stats.learned.current.clauses,
	   current_length (),
	     avg_height (),
	   avg_range (),
	     avg_density (),
	   top_level_assigned
#endif
    );

  fflush (output);
}

/*------------------------------------------------------------------------*/

static int
all_propagated (void)
{
  assert (0 <= next_propagation);
  assert (next_propagation <= count_stack (trail));
  return next_propagation == count_stack (trail);
}

/*------------------------------------------------------------------------*/

static void
restart (void)
{
  assert (level > 0);
  assert (conflicts_limit_for_restart <= stats.conflicts);
  assert (all_propagated ());
  INC (restarts);
#if defined(BOOLEFORCE_LOG) && defined(BOOLEFORCE_STATS)
  if (verbose >= 3)
    fprintf (output, "c restart %d\n", stats.restarts);
#endif
  undo (0);
  progress_report ('r');

  inc_restart_limit ();
  inc_reduce_limit (10);
}

/*------------------------------------------------------------------------*/

static int
decide_phase (int idx)
{
  /* TODO: what about most recent phase or most efficient phase?
   */
  (void) idx;
#ifdef USE_ZERO_PHASE_AS_DEFAULT
  return -1;
#else
  return rng_one_out_of_two_to_the_power (1) ? -1 : 1;	/* random phase */
#endif
}

/*------------------------------------------------------------------------*/

static int
random_decision (void)
{
  int sign, idx, res;
  unsigned pos;

  INC (random_decisions);

  res = 0;
  while (!res)
    {
      assert (count_stack (ranking));

      pos = rng ();
      pos %= count_stack (ranking);

      idx = pop_ranking (pos);
      if (deref_idx (idx) != UNKNOWN)
	continue;

      sign = rng_one_out_of_two_to_the_power (1) ? -1 : 1;
      res = sign * idx;
    }
#ifdef BOOLEFORCE_LOG
  if (verbose >= 4)
    fprintf (output, "c random decision %d\n", res);
#endif
  return res;
}

/*------------------------------------------------------------------------*/

static int
score_decision (void)
{
  int res, sign, idx;

  INC (score_decisions);

  res = 0;
  while (!res)
    {
      assert (count_stack (ranking));
      idx = pop_ranking (0);
      if (deref_idx (idx) != UNKNOWN)
	continue;

      sign = decide_phase (idx);
      res = sign * idx;
    }
#ifdef BOOLEFORCE_LOG
  if (verbose >= 4)
    fprintf (output, "c regular score decision %d\n", res);
#endif
  return res;
}

/*------------------------------------------------------------------------*/

static int
assume_decision (void)
{
  int *p, res, tmp;

  INC (assume_decisions);

  res = 0;
  for (p = assumptions.start; !res && p < assumptions.last; p++)
    {
      tmp = *p;
      if (deref_idx (tmp) == UNKNOWN)
	res = tmp;
    }
#ifdef BOOLEFORCE_LOG
  if (res && verbose >= 4)
    fprintf (output, 
	     "c forcing %d. assumption as decision %d\n",
	     (int)(p - assumptions.start), res);
#endif
  return res;
}

/*------------------------------------------------------------------------*/

static void
decide (void)
{
  unsigned coin;
  int decision;

  assert (unassigned > 0);
  assert (!empty_clause);
  assert (!conflict);

  decision = assume_decision ();
  if (!decision)
    {
      coin = rng_one_out_of_two_to_the_power (6);
      if (coin == 1)
	decision = random_decision ();
      else
	decision = score_decision ();
    }
  assert (decision);
  push_decision (decision);
}

/*------------------------------------------------------------------------*/

static int
all_variables_assigned (void)
{
  int res;

  if ((res = !unassigned))
    {
#ifdef BOOLEFORCE_LOG
      if (verbose >= 3)
	fprintf (output, "c no more unassigned variables\n");
#endif
    }

  return res;
}

/*------------------------------------------------------------------------*/

static void
bcp (void)
{
  int idx;

  assert (!empty_clause);

  INC (bcps);

  while (!conflict && !all_propagated ())
    {
      idx = trail.start[next_propagation++];
      assert (deref_idx (idx) == TRUE);
      propagate (idx);
    }

#ifndef NDEBUG
  if (check > 2)
    {
      check_all_watch_list_correct ();
      if (!conflict)
	check_no_clause_unsatisfied ();
    }
#endif
}

/*------------------------------------------------------------------------*/

static void
check_all_variables_unmarked (void)
{
#ifndef NDEBUG
  int i;

  if (check < 2)
    return;

  for (i = 1; i <= max_variable_idx; i++)
    assert (!idx2var(i)->mark);
#endif
}

/*------------------------------------------------------------------------*/

static int
all_variables_marked_in_clause (Clause * clause)
{
  int *p, *eoc, res;

  assert (clause);

  res = 1;
  eoc = end_of_cells (clause);
  for (p = clause->cells; res && p < eoc; p++)
    res = idx2var (*p)->mark;

  return res;
}

/*------------------------------------------------------------------------*/

static void
inc_resolved_literals (void)
{
  int * p, idx;

  for (p = resolved_literals.start; p < resolved_literals.last; p++)
    {
      idx = *p;
      inc_var_score_and_update_ranking (idx);
    }
}


/*------------------------------------------------------------------------*/

static void
update_incs (void)
{
  inc_var_score_inc ();
  inc_clause_score_inc ();
}

/*------------------------------------------------------------------------*/

static void
reset_resolved_literals (int count)
{
  int idx, *p, *start;
  Var *v;

  assert (count >= 0);
  start = resolved_literals.start + count;
  assert (start <= resolved_literals.last);
  for (p = start; p < resolved_literals.last; p++)
    {
      idx = *p;
      v = idx2var (idx);
      assert (v->mark > 0);
      v->mark = 0;
    }
#ifdef BOOLEFORCE_LOG
    if (verbose >= 5)
      {
	if (count)
	  fprintf (output,
	           "c removed %d resolved literals\n",
		   count_stack (resolved_literals) - count);
	else
	  fprintf (output,
		   "c removed all %d resolved literals sofar\n",
		   count_stack (resolved_literals));
      }
#endif
  resolved_literals.last = start;
}

/*------------------------------------------------------------------------*/
/* Try to produce a decision only learned clause of size smaller than
 * 'small_decision_clauses_size'.   If this succeeds put all traversed
 * literals on the 'resolved_literals' stack and return 1.  Otherwise remove
 * all temporarily pushed resolved literals and return 0.  The latter case
 * does not have any side effect (beside log messages).
 */
static int
resolve_until_decisions (void)
{
  int res, idx, other_idx, * p, * eoc, count, new_uip;
  Var *v;

  check_all_variables_unmarked ();
  assert (empty_stack (dfs_stack));
  assert (empty_stack (resolved_literals));
  assert (conflict);
  assert (!uip);

  eoc = end_of_cells (conflict);
  for (p = conflict->cells; p < eoc; p++)
    push_stack (dfs_stack, *p);

  res = 1;
  count = 0;
  new_uip = 0;
  while (res && !empty_stack (dfs_stack))
    {
      idx = pop_stack (dfs_stack);
      assert (deref_idx (idx) == FALSE);

      v = idx2var (idx);
      if (v->mark)
	continue;

      v->mark = 1;
      push_stack (resolved_literals, idx);

      if (v->reason)
	{
	  eoc = end_of_cells (v->reason);
	  for (p = v->reason->cells; p < eoc; p++)
	    {
	      other_idx = *p;
	      if (other_idx == -idx)
		continue;

	      assert (other_idx != idx);
	      push_stack (dfs_stack, other_idx);
	    }
	}
      else if (++count > small_decision_clause_size)
	res = 0;
      else if (v->level == level)
	new_uip = idx;
    }

  if (res)
    {
#ifdef BOOLEFORCE_LOG
      for (p = resolved_literals.start; p < resolved_literals.last; p++)
	log_addition_of_resolved_literal (*p);

      if (verbose >= 4)
	fprintf (output, 
	  "c generated decisions only resolvent of size %d\n",
	  count);
#endif
      uip = new_uip;
      INC (small_decision_clauses);
      ADD (small_decision_clauses_sum, count);
    }
  else
    {
#ifdef BOOLEFORCE_LOG
      if (verbose >= 4)
	fprintf (output, 
	  "c failed to generate decisions only resolvent of size %d\n",
	  small_decision_clause_size);
#endif
      reset_resolved_literals (0);
      reset_stack (dfs_stack, 0);
    }

  return res;
}

/*------------------------------------------------------------------------*/
/* Generate a first or last UIP clause, depending on whether
 * 'disable_first_uip' is non zero.  Add all resolved literals traversed to
 * the 'resolved_literals' stack and set the global 'uip' index to the UIP
 * found.
 */
static void
resolve_until_uip (void)
{
  int * p, * q, * eoc, i, j, count;
  Clause * reason;
  Var * v, * u;

  check_all_variables_unmarked ();
  assert (empty_stack (resolved_literals));
  assert (conflict);
  assert (!uip);

  count = 0;
  eoc = end_of_cells (conflict);
  for (p = conflict->cells; p < eoc; p++)
    {
      i = *p;
      v = idx2var (i);
      assert (!v->mark);

      v->mark = 1;
      add_resolved_literal (i);

      if (v->level == level)
	count++;
    }

  assert (count);
  reason = 0;			/* needed to detect first UIPs */

  p = trail.last;
  while (!uip)
    {
      assert (p > trail.start);

      i = *--p;
      v = idx2var (i);

      assert (v->level == level);

      if (!v->mark)
	continue;

      assert (count > 0);
      count--;

      reason = v->reason;

      if (count > 0 || (disable_first_uip && reason))
	{
	  if (reason)
	    {
	      eoc = end_of_cells (reason);
	      for (q = reason->cells; q < eoc; q++)
		{
		  j = *q;
		  u = idx2var (j);

		  assert (u->mark >= 0);
		  if (u->mark)
		    continue;

		  u->mark = 1;
		  add_resolved_literal (j);

		  if (u->level == level)
		    count++;
		}
	    }
	}
      else
	uip = -i;
    }

  assert (uip);

  if (reason)
    {
#ifdef BOOLEFORCE_LOG
      if (verbose >= 5)
	fprintf (output, "c found real first uip %d\n", uip);
#endif
      INC (uips);
    }

#ifdef BOOLEFORCE_LOG
  if (verbose >= 4)
    fprintf (output,
	     "c resolved %d literals while generating uip resolvent\n",
	     count_stack (resolved_literals));
#endif
}

/*------------------------------------------------------------------------*/

static void
check_legal_frame (Frame * frame)
{
  (void) frame;
  assert (control.start <= frame);
  assert (frame < control.last);
}

/*------------------------------------------------------------------------*/

static int
frame2level (Frame * frame)
{
  check_legal_frame (frame);
  return frame - control.start;
}

/*------------------------------------------------------------------------*/

static void
resolve_implication_chains_in_frame (Frame * frame)
{
  int * p, * last, * q, * eoc, this, other, frame_level, expand, marked;
  Clause * reason;
  Var * v, * u;

  frame_level = frame2level (frame);
  if (frame_level == level)
    {
      assert (frame->trail.last == -1);
      return;
    }

  frame->premisses.start = count_stack (resolved_premisses);

  p = trail.start + frame->trail.last;
  last = trail.start + frame->trail.start;

  while (p > last)
    {
      this = *--p;
      v = idx2var (this);
      assert (v->level == frame_level);
      if (!v->mark)
	continue;

      reason = v->reason;
      if (!reason)
	{
	  assert (p == last);
	  break;
	}

      if (disable_resolution_of_non_binary_implication_chains &&
	  reason->size > 2)
	break;

      marked = 0;
      expand = 1;
      eoc = end_of_cells (reason);
      for (q = reason->cells; expand && q < eoc; q++)
	{
	  other = *q;
	  u = idx2var (other);
	  assert (u->level <= v->level);
	  if (u->mark)
	    {
	      marked++;
	      continue;
	    }

	  expand = (u->level == frame_level);
	}

      if (expand)
	expand = (marked < reason->size);

#ifdef BOOLEFORCE_LOG
      if (verbose >= 5)
	{
	  if (expand)
	    fprintf (output, 
		     "c resolving clause %d "
		     "in implication chain at level %d\n",
		     reason->idx, frame_level);
	}
#endif
      if (!expand)
	continue;

      INC (resolved_implications);

      for (q = reason->cells; q < eoc; q++)
	{
	  other = *q;
	  u = idx2var (other);
	  if (u->mark)
	    continue;

	  u->mark = 1;
	  push_stack (resolved_premisses, other);
	  INC (resolved_premisses);
#ifdef BOOLEFORCE_LOG
	  if (verbose >= 5)
	    fprintf (output, "c resolving premisse %d\n", other);
#endif
	}
    }

  frame->premisses.last = count_stack (resolved_premisses);
}

/*------------------------------------------------------------------------*/

static void
resolve_implication_chains (void)
{
  Frame ** p;

  if (disable_resolution_of_implication_chains)
    return;

  INC (resolved_implication_chains);

  assert (empty_stack (resolved_premisses));
  for (p = frames.start; p < frames.last; p++)
    resolve_implication_chains_in_frame (*p);

#ifdef BOOLEFORCE_LOG
  if (verbose >= 4)
    fprintf (output,
	     "c resolved %d implication chains\n",
	     count_stack (resolved_premisses));
#endif
}

/*------------------------------------------------------------------------*/

static void
reset_resolved_premisses (void)
{
  int *p, idx;
  Var * v;

  for (p = resolved_premisses.start; p < resolved_premisses.last; p++)
    {
      idx = *p;
      v = idx2var (idx);
      if (!v->mark)
	continue;

      add_resolved_literal (idx);
    }

  reset_stack (resolved_premisses, 0);
}

/*------------------------------------------------------------------------*/

static void
trim_implication_chains (void)
{
  if (disable_resolution_of_implication_chains)
    return;

  if (!disable_trimming_of_implication_chains)
    {
    }

  reset_resolved_premisses ();
}

/*------------------------------------------------------------------------*/

static int
recursively_resolve_literal (int start_idx)
{
  int old_count_resolved_literals, res, idx, other_idx, * p, * eoc;
#ifndef NDEBUG
  int found;
#endif
  Clause * reason;
  Var * v;

  assert (empty_stack (dfs_stack));

  old_count_resolved_literals = count_stack (resolved_literals);
  push_stack (dfs_stack, start_idx);

  res = 1;
  while (res && count_stack (dfs_stack))
    {
      idx = pop_stack (dfs_stack);
      assert (deref_idx (idx) == FALSE);

      v = idx2var (idx);
      if (idx != start_idx)
	{
	  if (v->mark)
	    continue;

	  if (control.start[v->level].mark)
	    {
	      v->mark = 1;
	      push_stack (resolved_literals, idx);
	    }
	  else
	    {
	      res = 0;
	      break;
	    }
	}
      else
	assert (v->mark);

      reason = v->reason;
      if (reason && reason->size > 1)
	{
#ifndef NDEBUG
	  found = 0;
#endif
	  eoc = end_of_cells (reason);
	  for (p = reason->cells; p < eoc; p++)
	    {
	      other_idx = *p;
	      if (other_idx != -idx)
		{
		  assert (other_idx != idx);
		  push_stack (dfs_stack, other_idx);
		}
#ifndef NDEBUG
	      else
		found = 1;
#endif
	    }
	  assert (found);
	}
      else
	res = 0;
    }

  if (res)
    {
#ifdef BOOLEFORCE_LOG
      if (verbose >= 4)
	{
	  fprintf (output, "c recursively resolved literal %d\n", start_idx);

	  for (p = resolved_literals.start + old_count_resolved_literals;
	       p < resolved_literals.last;
	       p++)
	    log_addition_of_resolved_literal (*p);
	}
#endif
    }
  else
    {
#ifdef BOOLEFORCE_LOG
      if (verbose >= 4)
	fprintf (output, 
	         "c could not recursively resolve literal %d\n",
		 start_idx);
		 
#endif
      reset_resolved_literals (old_count_resolved_literals);
      reset_stack (dfs_stack, 0);
    }

  return res;
}

/*------------------------------------------------------------------------*/

static void
recursively_resolve_literals (void)
{
  int i, resolved, count, idx;

  if (disable_recursive_resolution_of_literals)
    return;

  resolved = 0;
  count = count_stack (resolved_literals);
  for (i = 0; i < count; i++)
    {
      /* 'recursively_resolve_literal' may change 'resolved_literals'.
       */
      idx = resolved_literals.start[i];
      if (idx == uip)
	continue;

      resolved += recursively_resolve_literal (idx);
    }
}

/*------------------------------------------------------------------------*/
#ifdef BOOLEFORCE_LOG
#define MSG(str) do { msg = str; } while (0)
#else
#define MSG(str) do { } while (0)
#endif
/*------------------------------------------------------------------------*/

static void
shrink_resolved_literals (void)
{
  int * p, * q, idx, keep;
  Clause * reason;
  Var * v;
#ifdef BOOLEFORCE_LOG
  int count = count_stack (resolved_literals), removed = 0;
  const char * msg;
#endif
#if defined(BOOLEFORCE_STATS) || defined(BOOLEFORCE_LOG)
  int max_size, actual_size, actually_removed;
#endif
#if defined(BOOLEFORCE_LOG) || defined(BOOLEFORCE_STATS)
  max_size = 0;

  if (level)
    {
      assert (uip);
      for (p = resolved_literals.start; p < resolved_literals.last; p++)
	{
	  idx = *p;

	  if (idx != uip)
	    {
	      assert (idx != -uip);

	      v = idx2var (idx);

	      if (v->level == level)
		continue;

	      if (!v->level)
		continue;
	    }
	  
	  max_size++;
	}
    }

  ADD (unshrunken_literals, max_size);
#endif
#ifdef BOOLEFORCE_LOG
  if (verbose >= 4)
    {
      fprintf (output, "c starting to shrink %d resolved literals\n", count);
      fprintf (output, "c expected maximal size %d\n", max_size);
    }
#endif
  for (p = resolved_literals.start; p < resolved_literals.last; p++)
    {
      idx = *p;
      v = idx2var (idx);
      assert (v->mark > 0);
      reason = v->reason;

      keep = 1;

      if (reason)
	{
	  if (level > 0)
	    {
	      if (idx != uip)
		{
		  if (all_variables_marked_in_clause (reason))
		    {
		      if (!v->level)
			{
			  MSG ("unit");
			  keep = 0;
			}
		      else if (disable_all_shrinking && v->level < level)
			MSG ("upper");
		      else
			{
			  MSG ("redundant");
			  keep = 0;
			}
		    }
		  else
		    MSG ("essential");
		}
	      else
		{
		  assert (idx != -uip);
		  MSG ("uip");
		}
	    }
	  else
	    {
	      assert (!level);
	      assert (reason->size == 1);
	      MSG ("unit");
	      keep = 0;
	    }
	}
      else
	MSG ("decision");

      if (keep)
	{
#ifdef BOOLEFORCE_LOG
	  if (verbose >= 5)
	    fprintf (output, "c keeping %s resolved literal %d\n", msg, idx);
#endif
	  assert (v->mark > 0);
	}
      else
	{
#ifdef BOOLEFORCE_LOG
	  removed++;
	  if (verbose >= 5)
	    fprintf (output, "c removing %s resolved literal %d\n", msg, idx);
#endif
	  v->mark = -1;
	}
    }

#ifdef BOOLEFORCE_LOG
  if (verbose >= 4)
    {
      assert (removed <= count);
      fprintf (output, 
	       "c shrinked resolvent from %d to %d by %d literals\n",
	       count, count - removed, removed);
    }
#endif

  assert (empty_stack (resolved_clauses));
  add_resolved_clause (conflict);

  q = resolved_literals.start;
  for (p = resolved_literals.start; p < resolved_literals.last; p++)
    {
      idx = *p;
      v = idx2var (idx);
      assert (v->mark);

      if (v->mark < 0)
	{
	  assert (v->reason);
	  add_resolved_clause (v->reason);
	}
      else
	*q++ = idx;

      v->mark = 0;
    }
  resolved_literals.last = q;

#if defined(BOOLEFORCE_LOG) || defined(BOOLEFORCE_STATS)
  actual_size = count_stack (resolved_literals);
  assert (actual_size <= max_size);
  actually_removed = max_size - actual_size;
#endif
#ifdef BOOLEFORCE_STATS
  ADD (shrunken_literals, actually_removed);
  if (actually_removed)
    INC (shrunken_clauses);
#endif
#ifdef BOOLEFORCE_LOG
  if (verbose >= 4)
    fprintf (output,
	     "c shrinking actually removes %d literals (%.1f%%)\n",
	     actually_removed, PERCENT (actually_removed, max_size));
#endif
}

/*------------------------------------------------------------------------*/

static void
analyze_frames (void)
{
  int * p, tmp, min_level;
  Frame * frame;
#if defined(BOOLEFORCE_STATS) || !defined(NDEBUG) || defined(BOOLEFORCE_LOG)
  int density, range;
#endif

  INC (analyzed_frames);

  min_level = level;
  for (p = resolved_literals.start; p < resolved_literals.last; p++)
    {
      tmp = idx2var (*p)->level;
      frame = control.start + tmp;
      assert (frame < control.last);

      if (!frame->mark)
	{
	  push_stack (frames, frame);
#ifdef BOOLEFORCE_LOG
	  if (verbose >= 5)
	    fprintf (output, "c analyzing frame %d\n", tmp);
#endif
	  if (tmp < min_level)
	    min_level = tmp;
	}

      frame->mark++;
      assert (frame->mark);		/* no overflow */
    }


#if defined(BOOLEFORCE_STATS) || !defined(NDEBUG) || defined(BOOLEFORCE_LOG)
  range = level - min_level + 1;
  density = count_stack (frames);
#endif
  ADD (sum_conflict_frame_range, range);
  ADD (sum_conflict_frames, density);

  assert (density <= range);
#ifdef BOOLEFORCE_LOG
  if (verbose >= 4)
    fprintf (output,
	     "c analyzing %d frames at range [%d,%d] with density %.1f%%\n",
	     density, min_level, level,
	     PERCENT (density, range));
#endif
}

/*------------------------------------------------------------------------*/
/* Compare frames by their level.  Since the frames are sorted on the
 * 'control' stack by their decision level anyhow, we can as well just
 * compare their addresses.
 */
static int
cmp_frame (Frame * f, Frame * g)
{
  if (f < g)
    return -1;

  if (f > g)
    return 1;

  return 0;
}

/*------------------------------------------------------------------------*/

static void
sort_frames (void)
{
  unsigned count = count_stack (frames);
  booleforce_sort (Frame *, cmp_frame, frames.start, count, sort_stack);
}

/*------------------------------------------------------------------------*/

static void
log_frames (void)
{
#ifdef BOOLEFORCE_LOG
  Frame ** p, * frame;
  int frame_level;

  if (verbose < 5)
    return;

  for (p = frames.start; p < frames.last; p++)
    {
      frame = *p;
      frame_level = frame2level (frame);
      assert (0 <= frame_level);
      assert (frame_level <= level);
      fprintf (output, 
	       "c frame %d has %d variables\n", 
	       frame_level, frame->mark);
    }
#endif
}

/*------------------------------------------------------------------------*/

static void
reset_frames (void)
{
  Frame ** p, * frame;

  for (p = frames.start; p < frames.last; p++)
    {
      frame = *p;
      assert (frame->mark);
      frame->mark = 0;
    }

  reset_stack (frames, 0);
}

/*------------------------------------------------------------------------*/

static void
analyze (void)
{
  if (!resolve_until_decisions ())
    {
      resolve_until_uip ();
      inc_resolved_literals ();

      analyze_frames ();
      sort_frames ();
      log_frames ();
      resolve_implication_chains ();
      recursively_resolve_literals ();
      trim_implication_chains ();
    }
  else
    analyze_frames ();

  shrink_resolved_literals ();
  reset_frames ();

  update_incs ();
}

/*------------------------------------------------------------------------*/

static void
backtrack (void)
{
  int new_level, idx;
  Clause *clause;

  assert (conflict);

  INC (backtracks);

  analyze ();
  clause = add_derived_clause (1);

  if (clause->size)
    {
      new_level = determine_backtrack_level (clause);
      undo (new_level);
      idx = forced_literal (clause);

      assert (idx);
      assert (next_propagation == count_stack (trail));
      assign (clause, idx);
    }
  else
    undo (-1);
}

/*------------------------------------------------------------------------*/

static size_t
adjust_recycled_bytes (size_t old_bytes)
{
  size_t res, new_bytes;

  new_bytes = booleforce_current_bytes ();
  if (old_bytes > new_bytes)
    {
      res = old_bytes - new_bytes;
      ADD (recycled_bytes, res);
    }
  else
    res = 0;

#ifdef BOOLEFORCE_LOG
  if (verbose >= 4)
    fprintf (output, "c recyled %"INT64FMT" bytes\n", (int64) res);
#endif

  return res;
}

/*------------------------------------------------------------------------*/

static void
delete_clause (Clause * clause)
{
  booleforce_delete (clause, bytes_clause (clause->size));
}

/*------------------------------------------------------------------------*/

static void
recycle_clause (Clause * clause)
{
  assert (clause->size > 1);
  assert (clause->dying);
#ifdef BOOLEFORCE_LOG
  if (verbose >= 4)
    fprintf (output, "c recycling clause %d\n", clause->idx);
#endif
  assert (clauses.start[clause->idx] == clause);
  clauses.start[clause->idx] = 0;
#ifdef BOOLEFORCE_TRACE
  if (clause->antecedents)
    idx2antecedents.start[clause->idx] = 0;
#endif
  stats.recycled_clauses++;
  stats.recycled_literals += clause->size;

  delete_clause (clause);
}

/*------------------------------------------------------------------------*/

static void
recycle_clauses (void)
{
  Clause **p, **q, *clause;
  int recycle;

  q = dying_clauses.start;
  for (p = q; p < dying_clauses.last; p++)
    {
      clause = *p;

      assert (clause);
      assert (clause->dying);

      recycle = 1;
      if (clause->reason)
	recycle = 0;
#ifndef NDEBUG
      /* Keep original clauses for 'check_all_clauses_satisfied'.
       */
      else if (clause->original)
	recycle = 0;
#endif
#ifdef BOOLEFORCE_TRACE
      /* Proper reference counting not implemented yet.
       */
      else if (trace)
	recycle = 0;
#endif
      else if (clause->size <= 1)	/* can not handle unit clauses yet */
	recycle = 0;

      if (recycle)
	recycle_clause (clause);
      else
	*q++ = clause;
    }

  dying_clauses.last = q;
#ifdef BOOLEFORCE_LOG
  if (verbose >= 3)
    fprintf (output, "c recycled %d dying clauses\n", (int)(p - q));
#endif
}

/*------------------------------------------------------------------------*/

static void
fast_top_level_gc (void)
{
  size_t old_bytes = booleforce_current_bytes ();
  double start_time = booleforce_time_stamp (), delta;
  int * p, * q, * last_trail, * last_watch, idx, count;
  int clause_idx, other_idx;
#ifdef BOOLEFORCE_LOG
  int recycled_bytes;
#endif
  Clause * clause;
  Lit * lit;

#ifndef NDEBUG
  if (check)
    check_current_clause_stats ();
#endif
  assert (!level);
  assert (top_level_assigned >= tla_fast_gc);
  if (top_level_assigned == tla_fast_gc)
    return;

  INC (fast_top_level_gcs);
#ifdef BOOLEFORCE_LOG
  if (verbose >= 3)
    fprintf (output,
	     "c starting fast top level garbage collection\n"
	     "c partially killing satisfied clauses\n");
#endif
  assert (top_level_assigned == (unsigned) count_stack (trail));

  count = 0;
  last_trail = trail.start + tla_fast_gc;
  p = trail.last;
  while (p > last_trail)
    {
      idx = *--p;
#ifdef BOOLEFORCE_LOG
      if (verbose >= 4)
	fprintf (output,
	         "c disconnecting, killing and recycling clauses with %d\n",
		 idx);
#endif
      assert (deref_idx (idx) == TRUE);
      lit = idx2lit (idx);

      last_watch = lit->watch2.last;
      for (q = lit->watch2.start; q < last_watch; q++)
	{
	  clause_idx = *q;
	  if (!clause_idx)
	    continue;

	  clause = idx2clause (clause_idx);

#ifdef BOOLEFORCE_LOG
	  if (verbose >= 4)
	    fprintf (output, "c disconnecting clause %d\n", clause_idx);
#endif
	  if (clause->size >= 2)
	    {
	      if (clause_idx < 0)
		{
		  other_idx = *++q;
		}
	      else 
		{
		  if (clause->cells[0] == idx)
		    other_idx = clause->cells[1];
		  else
		    {
		      assert (clause->cells[1] == idx);
		      other_idx = clause->cells[0];
		    }

		}

	      remove_watch (clause_idx, other_idx);
#ifndef NDEBUG
	      assert (clause->connected);
	      clause->connected = 0;
#endif
	    }
	  else
	    {
	      /* TODO: units? */
	    }

	  kill_clause (clause);
	  count++;
	}

      release_stack (lit->watch2);
    }

  recycle_clauses ();

#ifdef BOOLEFORCE_LOG
  recycled_bytes =
#else
  (void)
#endif
  adjust_recycled_bytes (old_bytes);


  tla_fast_gc = top_level_assigned;
#ifdef BOOLEFORCE_LOG
  if (verbose >= 3)
    fprintf (output, 
	     "c killed %d clauses in partial top level gc and "
	     "recycled %"INT64FMT" bytes\n",
	     count, (int64) recycled_bytes);
#endif
  delta = booleforce_time_stamp () - start_time;
  delta = (delta < 0) ? 0 : delta;
  ADD (gc_time, delta);
#ifdef BOOLEFORCE_LOG
  if (verbose >= 3)
    fprintf (output,
	     "c fast partial top level gc "
	     "%" INT64FMT " bytes "
	     "%d clauses "
	     "in %.2f seconds\n",
	     (int64) recycled_bytes, count, delta);
#endif
#ifndef NDEBUG
  if (check)
    check_current_clause_stats ();
#endif
}

/*------------------------------------------------------------------------*/

static int
cmp_failed_literals (int a, int b)
{
#if defined (USE_BINREFS_TO_ARBITRATE) || defined (USE_DLIS_TO_ARBITRATE)
  int res;
#endif

#ifdef USE_BINREFS_TO_ARBITRATE
  if ((res = cmp_sumbinrefs (a, b)))
    return -res;
#endif

#ifdef USE_DLIS_TO_ARBITRATE
  if ((res = cmp_sumrefs (a, b)))
    return res;
#endif

  assert (a > 0);
  assert (b > 0);

  return cmp_int (a, b);
}

/*------------------------------------------------------------------------*/

static void
remember_tla_of_literals_assigned_at_level_one (void)
{
  int * p, idx, tmp;

  assert (!conflict);
  assert (level == 1);

  p = trail.last;
  while (p > trail.start)
    {
      idx = *--p;
      tmp = idx2level (idx);
      if (!tmp)
	break;

      assert (tmp == 1);
      idx2lit(idx)->tla = top_level_assigned;
    }
}

/*------------------------------------------------------------------------*/

static void
failed_literals (void)
{
  int round, count, old_count, flipped;
  int *p, *q, idx, sign, decision;
  intStack stack;
#if defined(BOOLEFORCE_LOG) || defined(BOOLEFORCE_STATS)
  unsigned old_unassigned = unassigned;
#endif
#if defined(BOOLEFORCE_LOG)
  unsigned unassigned_before_round;
#endif

  if (disable_failed_literals)
    return;

  init_stack (stack);
  for (p = ranking.start; p < ranking.last; p++)
    {
      idx = *p;
      push_stack (stack, idx);
    }

  booleforce_sort (int, cmp_failed_literals,
		   stack.start, count_stack (stack), sort_stack);

  round = 0;
  old_count = -1;
  count = 0;

  disable_inc_score = 1;

  while (!empty_clause && unassigned > 0 && old_count < count)
    {
#if defined(BOOLEFORCE_LOG)
      unassigned_before_round = unassigned;
#endif
      old_count = count;

      round++;

      q = stack.start;
      for (p = stack.start; !empty_clause && p < stack.last; p++)
	{
	  idx = *p;

	  sign = -1;
	  for (flipped = 0; !flipped; flipped++, sign *= -1)
	    {
	      decision = sign * idx;
	      if (deref_idx (decision) != UNKNOWN)
		break;

	      if (idx2lit (decision)->tla == top_level_assigned)
		continue;

#ifdef BOOLEFORCE_LOG
	      if (verbose >= 4)
		fprintf (output,
			 "c failed literal test for %d in round %d\n",
			 decision, round);
#endif
	      push_decision (decision);

	      bcp ();
	      if (conflict)
		{
		  count++;

		  backtrack ();
		  assert (!level);

		  bcp ();
		  if (conflict)
		    {
		      backtrack ();
		      assert (empty_clause);
		      break;
		    }

		  fast_top_level_gc ();
		}
	      else
		{
		  remember_tla_of_literals_assigned_at_level_one ();
		  undo (0);
		}

	      if (stats.decisions && !(stats.decisions % 10000))
		progress_report	('f');
	    }

	  if (deref_idx (idx) == UNKNOWN)
	    *q++ = idx;
	}

      stack.last = q;

#ifdef BOOLEFORCE_LOG
      assert (unassigned_before_round >= unassigned);
      if (!empty_clause && verbose >= 3)
	fprintf (output,
		 "c round %d with %d failed literals and %d assignments\n",
		 round,
		 count - old_count, unassigned_before_round - unassigned);
#endif
    }

  disable_inc_score = 0;

#ifdef BOOLEFORCE_LOG
  assert (old_unassigned >= unassigned);
  if (verbose >= 3)
    fprintf (output,
	     "c %d failed literals and %d assignments\n",
	     count, old_unassigned - unassigned);
#endif
#ifdef BOOLEFORCE_STATS
  stats.failed_literals += count;
  stats.failed_literal_rounds += round;
  assert (old_unassigned >= unassigned);
  stats.assignments_through_failed_literals += old_unassigned - unassigned;
#endif
  release_stack (stack);
}

/*------------------------------------------------------------------------*/

static int
preprocess (void)
{
#ifdef BOOLEFORCE_LOG
  double start_time = booleforce_time_stamp ();
#endif
  unsigned old_unassigned = unassigned;
  int res;
  failed_literals ();
  res = old_unassigned - unassigned;
#ifdef BOOLEFORCE_LOG
  if (verbose >= 3)
    booleforce_report (start_time, output,
		       "c preprocessing produced %d assignments", res);
#endif
  progress_report ('p');

  return res || empty_clause;
}

/*------------------------------------------------------------------------*/

static void
flush_progress_report (void)
{
  if (flushed_report)
    return;

  if (!verbose)
    return;

  if (!stats.progress_reports)
    return;

  progress_report ('.');
  flushed_report = 1;
}

/*------------------------------------------------------------------------*/

static int
exhausted (void)
{
  double time;

  if (limits.conflicts >= 0 && stats.conflicts >= limits.conflicts)
    {
      flush_progress_report ();
      if (verbose)
	fprintf (output,
		 "c limit of %d conflicts reached\n", limits.conflicts);

      return 1;
    }

  if (limits.decisions >= 0 && stats.decisions >= limits.decisions)
    {
      flush_progress_report ();
      if (verbose)
	fprintf (output,
		 "c limit of %d decisions reached\n", limits.decisions);
      return 1;
    }

  if (limits.time >= 0)
    {
      time = adjusted_seconds ();
      if (time >= limits.time)
	{
	  flush_progress_report ();
	  if (verbose)
	    fprintf (output,
		     "c time limit %.2f seconds reached after %.2f seconds\n",
		     limits.time, time);
	  return 1;
	}
    }

  return 0;
}

/*------------------------------------------------------------------------*/

static int
clause_top_level_satisfied (Clause * clause)
{
  int *p, *eoc = end_of_cells (clause), idx;

  for (p = clause->cells; p < eoc; p++)
    {
      idx = *p;

      if (idx2level (idx) > 0)
	continue;

      if (deref_idx (idx) == TRUE)
	return 1;
    }

  return 0;
}

/*------------------------------------------------------------------------*/

static void
kill_top_level_satisfied_clauses (void)
{
  int killed_clauses, killed_literals;
  Clause **p, *clause;

  killed_clauses = killed_literals = 0;

  for (p = clauses.start; p < clauses.last; p++)
    {
      clause = *p;

      if (!clause)
	continue;

      if (clause->dying)
	continue;

      if (!clause_top_level_satisfied (clause))
	continue;

      killed_clauses++;
      killed_literals += clause->size;

      kill_clause (clause);
    }
#ifdef BOOLEFORCE_LOG
  if (verbose >= 3)
    fprintf (output,
	     "c killed %d literals in %d satisfied clauses\n",
	     killed_literals, killed_clauses);
#endif
}

/*------------------------------------------------------------------------*/

static void
prune_false_literals (int old_count)
{
  int pruned_clauses, pruned_literals, *q, *eoc, idx, count, tmp, i;
  Clause *clause, *reason;
  Var *var;

  assert (!level);
  pruned_clauses = pruned_literals = 0;

  assert (old_count <= count_stack (clauses));

  for (i = 1; i < old_count; i++)
    {
      assert (i < count_stack (clauses));
      clause = clauses.start[i];

      if (!clause)
	continue;

      if (clause->dying)
	continue;

      count = 0;
      eoc = end_of_cells (clause);
      for (q = clause->cells; q < eoc; q++)
	{
	  idx = *q;
	  tmp = deref_idx (idx);
	  assert (tmp != TRUE);
	  if (tmp == FALSE)
	    count++;
	}

      if (!count)
	continue;

      assert (empty_stack (resolved_literals));
      assert (empty_stack (resolved_clauses));

      add_resolved_clause (clause);

      for (q = clause->cells; q < eoc; q++)
	{
	  idx = *q;
	  tmp = deref_idx (idx);
	  if (tmp == FALSE)
	    {
#ifdef BOOLEFORCE_LOG
	      if (verbose >= 5)
		fprintf (output,
			 "c pruning literal %d from clause %d\n",
			 idx, clause->idx);
#endif
	      var = idx2var (idx);
	      assert (!var->level);

	      reason = var->reason;
	      assert (reason);
	      assert (reason->size == 1);
	      assert (reason->cells[0] == -idx);

	      add_resolved_clause (reason);
	    }
	  else
	    add_resolved_literal (idx);
	}

      pruned_literals += count;
      pruned_clauses++;

      add_derived_clause (0);
      kill_clause (clause);
    }
#ifdef BOOLEFORCE_LOG
  if (verbose >= 3)
    fprintf (output,
	     "c pruned %d literals in %d clauses\n",
	     pruned_literals, pruned_clauses);
#endif
}

/*------------------------------------------------------------------------*/

static int
disconnect (void)
{
  int idx, count = 0;
  Lit *lit;
#ifdef BOOLEFORCE_LOG
  int *p, clause_idx;
#endif
#ifndef NDEBUG
  Clause **q, * clause;
#endif

  for (idx = -max_variable_idx; idx <= max_variable_idx; idx++)
    {
      if (!idx)
	continue;

      lit = idx2lit (idx);
#ifdef BOOLEFORCE_LOG
      if (verbose >= 3)
	{
	  for (p = lit->watch2.start; p < lit->watch2.last; p++)
	    {
	      clause_idx = *p;
	      count++;

	      if (clause_idx < 0)
		p++;
	    }
	}
#endif
      release_stack (lit->watch2);
    }

#ifdef BOOLEFORCE_LOG
  if (verbose >= 3)
    fprintf (output, "c disconnected %d watched clauses\n", count);
#endif

  if ((count = count_stack (unit_clauses)))
    {
      reset_stack (unit_clauses, 0);
#ifdef BOOLEFORCE_LOG
      if (verbose >= 3)
	fprintf (output, "c disconnected %d unit clauses\n", count);
#endif
    }

  if (empty_clause)
    {
      empty_clause = 0;
#ifdef BOOLEFORCE_LOG
      if (verbose >= 3)
	fprintf (output, "c disconnected empty clause\n");
#endif
    }

#ifndef NDEBUG
  for (q = clauses.start; q < clauses.last; q++)
    {
      clause = *q;
      if (!clause)
	continue;

      clause->connected = 0;
    }
#endif

  return count_stack (clauses);
}

/*------------------------------------------------------------------------*/

static void
connect_live_clauses (int old_count)
{
  Clause **p, *clause, **last;
  int live;

  live = 0;
  last = clauses.start + old_count;
  assert (last <= clauses.last);

  for (p = clauses.start; p < last; p++)
    {
      clause = *p;

      if (!clause)
	continue;

      if (clause->dying)
	continue;

      live++;
      connect_clause (clause);
    }
#ifdef BOOLEFORCE_LOG
  if (verbose >= 3)
    fprintf (output, "c reconnected %d live clauses\n", live);
#endif
}

/*------------------------------------------------------------------------*/

static void
kill_top_level_satisfied_clauses_and_prune_false_literals (int old_count)
{
  kill_top_level_satisfied_clauses ();
  prune_false_literals (old_count);
}

/*------------------------------------------------------------------------*/

static int
cmp_learned_clause (int i, int j)
{
  Clause *a = idx2clause (i);
  Clause *b = idx2clause (j);
  int res;

  assert (a->learned);
  assert (b->learned);

  if ((res = booleforce_cmp_uwe (a->score, b->score)))
    return res;

  return cmp_int (a->idx, b->idx);
}

/*------------------------------------------------------------------------*/

static void
kill_less_active_learned_clauses (int old_count)
{
  int count_learned, count_binary, count_active, count_killed;
  int *q, limit, *first_not_killed;
  Clause **p, **last, *clause;

  assert (old_count == count_stack (clauses));
  kill_top_level_satisfied_clauses ();

  last = clauses.start + old_count;
  assert (last <= clauses.last);

  assert (empty_stack (reduce_learned_clauses_stack));

  for (p = clauses.start; p < last; p++)
    {
      clause = *p;

      if (!clause)
	continue;

      if (clause->dying)
        continue;

      if (!clause->learned)
	continue;

      push_stack (reduce_learned_clauses_stack, clause->idx);
    }

  count_learned = count_stack (reduce_learned_clauses_stack);
  assert (count_learned == stats.learned.current.clauses);
#ifdef BOOLEFORCE_LOG
  if (verbose >= 3)
    fprintf (output,
	     "c found %d learned candidate clauses for reduction\n",
	     count_learned);

#endif
  booleforce_sort (int, cmp_learned_clause,
		   reduce_learned_clauses_stack.start,
		   count_learned, sort_stack);
  limit = count_learned / 2;
  first_not_killed = reduce_learned_clauses_stack.start + limit;

  count_killed = 0;
  count_binary = 0;
  count_active = 0;

  for (q = reduce_learned_clauses_stack.start; q < first_not_killed; q++)
    {
      clause = idx2clause (*q);

      assert (clause);
      assert (!clause->dying);

      if (clause->reason)
	{
	  count_active++;
	  continue;
	}

      if (clause->size <= 2)
	{
	  count_binary++;
	  continue;
	}

#ifdef BOOLEFORCE_LOG
      if (verbose >= 4)
	{
	  fprintf (output, "c clause %d with low score ", clause->idx);
	  booleforce_print_uwe (clause->score, output);
	  fputc ('\n', output);
	}
#endif
      kill_clause (clause);
      count_killed++;
      INC (reduced_learned_clauses);
      ADD (reduced_learned_literals, clause->size);
    }
#ifdef BOOLEFORCE_LOG
  if (verbose >= 3)
    {
      fprintf (output,
	       "c killed %d low score clauses out of %d candidates\n",
	       count_killed, limit);

      fprintf (output,
	       "c kept %d active and %d binary clauses\n",
	       count_active, count_binary);

    }
#endif
  reset_stack (reduce_learned_clauses_stack, 0);

  inc_reduce_limit (1);
}

/*------------------------------------------------------------------------*/

static void
gc (void (*kill_and_add_clauses) (int))
{
  size_t old_bytes = booleforce_current_bytes ();
  double start_time = booleforce_time_stamp (), delta;
#ifdef BOOLEFORCE_LOG
  size_t recycled_bytes;
#endif
  int old_count;
#ifdef BOOLEFORCE_LOG
  int64 old_recycled_clauses = stats.recycled_clauses;
  int64 old_recycled_literals = stats.recycled_literals;
#endif
#ifndef NDEBUG
  if (check)
    check_current_clause_stats ();
#endif
  assert (!empty_clause);
  assert (all_propagated ());

  stats.gcs++;
#ifdef BOOLEFORCE_LOG
  if (verbose >= 3)
    fprintf (output, "c garbage collection %d\n", stats.gcs);
#endif
  old_count = disconnect ();
  kill_and_add_clauses (old_count);
  recycle_clauses ();
  connect_live_clauses (old_count);

#ifdef BOOLEFORCE_LOG
  recycled_bytes = 
#else
  (void)
#endif
  adjust_recycled_bytes (old_bytes);

  delta = booleforce_time_stamp () - start_time;
  delta = (delta < 0) ? 0 : delta;
  ADD (gc_time, delta);
#ifdef BOOLEFORCE_LOG
  if (verbose >= 3)
    fprintf (output,
	     "c gc "
	     "%" INT64FMT " bytes "
	     "%" INT64FMT " literals "
	     "%" INT64FMT " clauses "
	     "in %.2f seconds\n",
	     (int64) recycled_bytes,
	     stats.recycled_literals - old_recycled_literals,
	     stats.recycled_clauses - old_recycled_clauses, delta);
#endif
#ifndef NDEBUG
  if (check)
    {
      check_current_clause_stats ();
      if (check > 1)
	check_all_watch_list_correct ();
    }
#endif
}

/*------------------------------------------------------------------------*/

static void
full_top_level_gc (void)
{
  assert (!level);
  assert (top_level_assigned >= tla_full_gc);
  if (top_level_assigned == tla_full_gc)
    return;

  tla_fast_gc = tla_full_gc = top_level_assigned;

  INC (full_top_level_gcs);
#ifdef BOOLEFORCE_LOG
  if (verbose >= 3)
    fprintf (output,
	     "c starting full top level garbage collection\n"
	     "c killing satisfied clauses and pruning false literals\n");
#endif
  gc (kill_top_level_satisfied_clauses_and_prune_false_literals);
}

/*------------------------------------------------------------------------*/

static void
reduce_learned_clauses (void)
{
  assert (level > 0);
  INC (reduce_learned_clauses_gcs);
  assert (learned_limit_for_reduce <= stats.learned.current.clauses);
#ifdef BOOLEFORCE_LOG
  if (verbose >= 3)
    fprintf (output,
	     "c reducing %d learned clauses\n",
	     stats.learned.current.clauses);
#endif
  gc (kill_less_active_learned_clauses);
  progress_report ('-');
}

/*------------------------------------------------------------------------*/

static int
use_full_top_level_gc_in_iteration (void)
{
  int sum, inc;

  inc = 1;
  sum = 0;

  while (inc < 128)
    {
      sum += 10 * inc;				/* ten times inc */
      if (stats.iterations < sum)
	return !(stats.iterations & (inc - 1));

      inc *= 2;
    } 

  return !(stats.iterations & (inc - 1));	/* every 128th */
}

/*------------------------------------------------------------------------*/

static void
iteration (void)
{
  assert (!level);
  stats.iterations++;
#ifdef BOOLEFORCE_LOG
  if (verbose >= 3)
    fprintf (output,
	     "c iteration %d at %d top level assignments\n",
	     stats.iterations, top_level_assigned);
#endif

  if (use_full_top_level_gc_in_iteration ())
    full_top_level_gc ();
  else
    fast_top_level_gc ();

  progress_report ('i');
}

/*------------------------------------------------------------------------*/

static void
init_iteration (void)
{
  init_restart_limit ();
  init_reduce_limit ();
}

/*------------------------------------------------------------------------*/

static void
push_unit_clause (Clause * clause)
{
  int idx, tmp;

  assert (clause->size == 1);
  idx = clause->cells[0];
  tmp = deref_idx (idx);

  if (tmp == TRUE)
    return;

  if (tmp == FALSE)
    {
#ifdef BOOLEFORCE_LOG
      if (verbose >= 4)
	fprintf (output, "c conflicting unit clause %d\n", clause->idx);
#endif
      push_conflict (clause);
    }
  else
    assign (clause, idx);
}

/*------------------------------------------------------------------------*/

static void
push_unit_clauses (void)
{
  int i;

  assert (!conflict);
  for (i = 0; !conflict && i < count_stack (unit_clauses); i++)
    push_unit_clause (idx2clause (unit_clauses.start[i]));
}

/*------------------------------------------------------------------------*/

static int
restart_limit_reached (void)
{
  return conflicts_limit_for_restart <= stats.conflicts;
}

/*------------------------------------------------------------------------*/

static int
reduce_limit_reached (void)
{
  int current = stats.learned.current.clauses;

  current -= assigned;

  return learned_limit_for_reduce <= current;
}

/*------------------------------------------------------------------------*/

static Result
sat (void)
{
  if (empty_clause)
    return FALSE;

  if (count_stack (unit_clauses))
    {
      push_unit_clauses ();

      if (!conflict)
	bcp ();

      if (conflict)
	{
	  backtrack ();
	  assert (empty_clause);
	  return FALSE;
	}

      full_top_level_gc ();
    }

  progress_report ('u');

  if (preprocess ())
    {
      if (empty_clause)
	return FALSE;

      full_top_level_gc ();
    }

  if (all_variables_assigned ())
    return TRUE;

  if (exhausted ())
    return UNKNOWN;

  init_iteration ();

  decide ();

  for (;;)
    {
      bcp ();
      if (conflict)
	{
	  backtrack ();

	  if (empty_clause)
	    return FALSE;
	}
      else
	{
	  if (all_variables_assigned ())
	    return TRUE;

	  if (exhausted ())
	    return UNKNOWN;

	  if (level)
	    {
	      if (restart_limit_reached ())
		restart ();

	      if (reduce_limit_reached ())
		reduce_learned_clauses ();
	    }
	  else
	    iteration ();

	  decide ();
	}
    }
}

/*------------------------------------------------------------------------*/

void
booleforce_assume (int lit)
{
  assert (lit);
  push_stack (assumptions, lit);
}

/*------------------------------------------------------------------------*/

int
booleforce_sat (void)
{
  int tmp, res;

  booleforce_enter ();

  tmp = sat ();
#ifndef NDEBUG
  if (tmp == TRUE)
    check_all_clauses_satisfied ();
#endif
  flush_progress_report ();

  switch (tmp)
    {
    case TRUE:
      res = BOOLEFORCE_SATISFIABLE;
      break;
    case FALSE:
      res = BOOLEFORCE_UNSATISFIABLE;
      break;
    default:
      assert (tmp == UNKNOWN);
      res = BOOLEFORCE_UNKNOWN;
      break;
    }

  booleforce_leave ();

  return res;
}

/*------------------------------------------------------------------------*/

int
booleforce_deref (int a)
{
  int res;

  assert (a > 0);
  booleforce_enter ();

  if (a > max_variable_idx)
    res = UNKNOWN;
  else
    res = deref_idx (a);

  booleforce_leave ();

  return res;
}

/*------------------------------------------------------------------------*/

static void
release_clauses (void)
{
  Clause **p;

  for (p = clauses.start; p < clauses.last; p++)
    {
      if (!*p)
	continue;

      delete_clause (*p);
    }
}

/*------------------------------------------------------------------------*/

static void
release_literal (Lit * lit)
{
  release_stack (lit->watch2);
}

/*------------------------------------------------------------------------*/

static void
release_literals (void)
{
  int i;

  if (!literals)
    return;

  for (i = 1; i <= max_variable_idx; i++)
    {
      release_literal (idx2lit (i));
      release_literal (idx2lit (-i));
    }

  booleforce_delete (literals, bytes_literals (size_variables));
  literals = 0;
}

/*------------------------------------------------------------------------*/

static void
release_assignment (void)
{
  booleforce_delete (assignment, size_variables);
}

/*------------------------------------------------------------------------*/

static void
release_variables (void)
{
  booleforce_delete (variables, bytes_variables (size_variables));
}

/*------------------------------------------------------------------------*/

void
booleforce_set_check (int level)
{
  (void) level;
  booleforce_enter ();
#ifndef NDEBUG
  check = (level < 0) ? 0 : level;
#endif
  booleforce_leave ();
}

/*------------------------------------------------------------------------*/

void
booleforce_set_verbose (int level)
{
  booleforce_enter ();
  verbose = (level < 0) ? 0 : level;
  booleforce_leave ();
}

/*------------------------------------------------------------------------*/

void
booleforce_set_trace (int enable_trace)
{
  (void) enable_trace;
  booleforce_enter ();
#ifdef BOOLEFORCE_TRACE
  trace = enable_trace ? 1 : 0;
#endif
  booleforce_leave ();
}

/*------------------------------------------------------------------------*/

void
booleforce_set_failed_literals (int enable_failed_literals)
{
  booleforce_enter ();
  if (enable_failed_literals)
    disable_failed_literals = 0;
  else
    disable_failed_literals = 1;
  booleforce_leave ();
}

/*------------------------------------------------------------------------*/

void
booleforce_set_output (FILE * file, const char * name)
{
  booleforce_enter ();
  assert (file);
  assert (name);
  output = file;
  output_name = name;
  booleforce_leave ();
}

/*------------------------------------------------------------------------*/

void
booleforce_set_seed (unsigned seed)
{
  booleforce_enter ();
  rng_state = rng_seed = seed;
  booleforce_leave ();
}

/*------------------------------------------------------------------------*/

void
booleforce_set_conflict_limit (int limit)
{
  booleforce_enter ();
  limits.conflicts = limit;
  booleforce_leave ();
}

/*------------------------------------------------------------------------*/

void
booleforce_set_decision_limit (int limit)
{
  booleforce_enter ();
  limits.decisions = limit;
  booleforce_leave ();
}

/*------------------------------------------------------------------------*/

void
booleforce_set_time_limit (double limit)
{
  booleforce_enter ();
  limits.time = limit;
  booleforce_leave ();
}

/*------------------------------------------------------------------------*/

void
booleforce_banner (void)
{
  fprintf (output, "c booleforce version %s\n", booleforce_version ());
  if (verbose >= 2)
    fprintf (output, "c %s\n", booleforce_id ());
}

/*------------------------------------------------------------------------*/

static void
log_boolean_option (int option, const char * msg)
{
  fprintf (output, "c %s %s\n", msg, option ? "enabled" : "disabled");
}

/*------------------------------------------------------------------------*/

void
booleforce_options (void)
{
  fprintf (output, "c output file '%s'\n", output_name);

#ifndef NDEBUG
  fprintf (output, "c checking level %d\n", level);
#else
  fputs ("c checking not supported\n", output);
#endif

  fprintf (output, "c verbose level %d\n", level);

#ifdef BOOLEFORCE_TRACE
  log_boolean_option (trace, "trace generation");
#else
  fputs ("c trace generation not supported\n", output);
#endif

  fprintf (output, "c random number generator seed %u\n", rng_seed);

  fputs ("c conflict limit ", output);
  if (limits.conflicts < 0)
    fputs ("none", output);
  else
    fprintf (output, "%d", limits.conflicts);
  fputc ('\n', output);

  fputs ("c decision limit ", output);
  if (limits.decisions < 0)
    fputs ("none", output);
  else
    fprintf (output, "%d", limits.decisions);
  fputc ('\n', output);

  fputs ("c time limit ", output);
  if (limits.time < 0)
    fputs ("none", output);
  else
    fprintf (output, "%.2f\n", limits.time);
  fputc ('\n', output);

  log_boolean_option (!disable_failed_literals, "failed literals");

  fprintf (output,
           "c small decision clause size %d\n", 
	   small_decision_clause_size);

  log_boolean_option (!disable_first_uip, "first uip");

  log_boolean_option (
    !disable_resolution_of_implication_chains,
    "resolution of implication chains");

  log_boolean_option (
    !disable_resolution_of_non_binary_implication_chains,
    "resolution of non-binary implication chains");

  log_boolean_option (
    !disable_recursive_resolution_of_literals,
    "recursive resolution of literals");

  log_boolean_option (
    !disable_trimming_of_implication_chains,
    "trimming of implication chains");

  log_boolean_option (!disable_all_shrinking, "shrinking in general");
}

/*------------------------------------------------------------------------*/

int
booleforce_disable (const char * option)
{
  int res;

  res = 1;

  if (!strcmp (option, "failed-literals"))
    disable_failed_literals = 1;
  else if (!strcmp (option, "resolution-of-implication-chains"))
    {
      disable_resolution_of_implication_chains = 1;
      disable_resolution_of_non_binary_implication_chains = 1;
      disable_trimming_of_implication_chains = 1;
    }
  else if (!strcmp (option, "resolution-of-non-binary-implication-chains"))
    disable_resolution_of_non_binary_implication_chains = 1;
  else if (!strcmp (option, "recursive-resolution-of-literals"))
    disable_recursive_resolution_of_literals = 1;
  else if (!strcmp (option, "trimming-of-implication-chains"))
    disable_trimming_of_implication_chains = 1;
  else if (!strcmp (option, "all-shrinking"))
    {
      disable_all_shrinking = 1;
      disable_resolution_of_implication_chains = 1;
      disable_resolution_of_non_binary_implication_chains = 1;
      disable_recursive_resolution_of_literals = 1;
      disable_trimming_of_implication_chains = 1;
    }
  else if (!strcmp (option, "first-uip"))
    disable_first_uip = 1;
  else
    res = 0;

  return res;
}

/*------------------------------------------------------------------------*/

void
booleforce_init (void)
{
  if (state == INITIALIZED_STATE)
    return;

  disable_recursive_resolution_of_literals = 0;		
  disable_resolution_of_non_binary_implication_chains = 1;
  disable_resolution_of_implication_chains = 1;
  disable_trimming_of_implication_chains = 1;
  disable_failed_literals = 1;

  limits.conflicts = -1;        /* no limit */
  limits.decisions = -1;        /* no limit */
  limits.time = -1;             /* no limit */

  small_decision_clause_size = 1;	/* TODO: no good inc_update */
 
  var_score_inc = booleforce_init_uwe (1, 0);
  clause_score_inc = booleforce_init_uwe (1, 0);

  output = stdout;

  level = -1;
  assert (empty_stack (control));
  push_frame ();
  assert (level == 0);

  state = INITIALIZED_STATE;
}

/*------------------------------------------------------------------------*/

void
booleforce_reset (void)
{
  int saved;

  if (state == RESET_STATE)
    return;

  release_stack (resolved_clauses);
  release_stack (dfs_stack);
  release_stack (resolved_literals);
  release_stack (resolved_premisses);
  release_stack (sort_stack);
  release_clauses ();
  release_stack (clauses);
#ifdef BOOLEFORCE_TRACE
  release_stack (antecedents);
  release_stack (idx2antecedents);
#endif
  release_stack (reduce_learned_clauses_stack);
  release_stack (unit_clauses);
  release_stack (dying_clauses);
  release_stack (trail);
  release_stack (control);
  release_stack (frames);
  release_stack (ranking);
  release_stack (assumptions);

  release_literals ();
  release_assignment ();
  release_variables ();
  size_variables = 0;

  booleforce_reset_mem ();

  /* clear all statically allocated memory.
   */
  saved = entered;
#define CLRSTATE(state) memset (&state, 0, sizeof (state))
#define STATEMACRO CLRSTATE
#include "booleforce.states"
#undef STATEMACRO
  assert (state == RESET_STATE);
  entered = saved;
}

/*------------------------------------------------------------------------*/

static void
print_clause (FILE * file, Clause * clause)
{
  int *q, *eoc;

  eoc = end_of_cells (clause);
  for (q = clause->cells; q < eoc; q++)
    fprintf (file, "%d ", *q);

  fputs ("0\n", file);
}

/*------------------------------------------------------------------------*/

static void
booleforce_print_clauses (FILE * file)
{
  Clause **p, *clause;

  for (p = clauses.start; p < clauses.last; p++)
    {
      clause = *p;
      if (!clause)
	continue;

      print_clause (file, clause);
    }
}

/*------------------------------------------------------------------------*/

void
booleforce_print (FILE * file)
{
  booleforce_enter ();
  fprintf (file,
	   "p cnf %d %d\n", max_variable_idx, stats.all.current.clauses);
  booleforce_print_clauses (file);
  booleforce_leave ();
}

/*------------------------------------------------------------------------*/
#ifdef BOOLEFORCE_TRACE
/*------------------------------------------------------------------------*/

static void
extract_clausal_core (void)
{
  int idx, antecedent_idx, *p, original, learned, resolved;
  double start_time;
  intStack stack;
  Clause *clause;

  if (clausal_core_generated)
    return;

  if (!empty_clause)
    return;

  start_time = booleforce_time_stamp ();

  original = 0;
  learned = 0;
  resolved = 0;
  init_stack (stack);

  push_stack (stack, empty_clause->idx);
  while (count_stack (stack))
    {
      idx = pop_stack (stack);
      clause = idx2clause (idx);
      if (clause->core)
	continue;

      clause->core = 1;

      if (clause->original)
	{
	  original++;
	  continue;
	}

      if (clause->resolved)
	resolved++;
      else
      {
	assert (clause->learned);
	learned++;
      }

      assert (clause->antecedents);
      for (p = clause2antecedents (clause); (antecedent_idx = *p); p++)
	push_stack (stack, antecedent_idx);
    }
  release_stack (stack);

#ifdef BOOLEFORCE_LOG
  if (verbose >= 2)
    {
      int all = original + learned + resolved;

      fprintf (output,
	       "c extracted %d original core clauses (%.0f%% out of %d)\n",
	       original, PERCENT (original, stats.original.max.clauses),
	       stats.original.max.clauses);
      fprintf (output,
	       "c extracted %d resolved core clauses (%.0f%% out of %d)\n",
	       resolved, PERCENT (resolved, stats.resolved.max.clauses),
	       stats.resolved.max.clauses);
      fprintf (output,
	       "c extracted %d learned core clauses (%.0f%% out of %d)\n",
	       learned, PERCENT (learned, stats.learned.max.clauses),
	       stats.learned.max.clauses);

      fprintf (output,
	       "c extracted %d core clauses (%.0f%% out of %d)\n",
	       all, PERCENT (learned, stats.all.max.clauses),
	       stats.all.max.clauses);
    }
#endif
  clausal_core_generated = 1;

  if (verbose)
    booleforce_report (start_time, output, "c extracted clausal core");
}

/*------------------------------------------------------------------------*/

static void
putint (int n, FILE * file)
{
  char buffer[((sizeof (int)) * 8 + 2) / 3 + 2];
  int i, m;

  if (n)
    {
      i = 0;
      m = n;
      do
	{
	  buffer[i++] = (m % 10) + '0';
	  m /= 10;
	}
      while (m);

      do
	{
	  putc (buffer[--i], file);
	}
      while (i);
    }
  else
    putc ('0', file);
}

/*------------------------------------------------------------------------*/

static void
print_antecedents_with_white_space (Clause * clause, FILE * file)
{
  int *p, idx;

  assert (clause->antecedents);
  for (p = clause2antecedents (clause); (idx = *p); p++)
    {
      putc (' ', file);
      putint (idx, file);
    }
  fputs (" 0", file);
}

/*------------------------------------------------------------------------*/

static void
print_clause_in_resolution_trace (Clause * clause, FILE * file, int extended)
{
  putint (clause->idx, file);

  if (extended || clause->original)
    {
      print_clause_with_white_space (clause, file);
      fputs (" 0", file);
    }
  else
    fputs (" *", file);		/* skip literals */

  if (clause->original)
    fputs (" 0", file);
  else
    print_antecedents_with_white_space (clause, file);

  fputc ('\n', file);
}

/*------------------------------------------------------------------------*/

static void
print_resolution_trace_from_core (FILE * file, int extended)
{
  Clause ** p, * clause;

  for (p = clauses.start; p < clauses.last; p++)
  {
    clause = *p;

    if (!clause)
      continue;

    if (!clause->core)
      continue;

    print_clause_in_resolution_trace (clause, file, extended);
  }
}

/*------------------------------------------------------------------------*/

void
booleforce_print_resolution_trace (FILE * file, int extended)
{
  booleforce_enter ();
  extract_clausal_core ();
  print_resolution_trace_from_core (file, extended);
  booleforce_leave ();
}

/*------------------------------------------------------------------------*/

static int
include_vars_of_clause_in_core (Clause * clause)
{
  int *p, *eoc = end_of_cells (clause), idx, count;
  Var *v;

  count = 0;
  for (p = clause->cells; p < eoc; p++)
    {
      idx = *p;
      v = idx2var (idx);
      if (v->core)
	continue;
      v->core = 1;
      count++;
#ifdef BOOLEFORCE_LOG
      if (verbose >= 4)
	fprintf (output, "c variable %d in core\n", (int)(v - variables));
#endif
    }

  return count;
}

/*------------------------------------------------------------------------*/

static void
extract_vars_in_core (void)
{
  Clause ** p, * clause;
  int count;

  assert (!vars_core_generated);

  extract_clausal_core ();
  count = 0;

  for (p = clauses.start; p < clauses.last; p++)
    {
      clause = *p;

      if (!clause)
	continue;

      if (!clause->core)
	continue;

      if (!clause->original)	/* we do not have extended resolution */
	continue;

      count += include_vars_of_clause_in_core (clause);
    }

#ifdef BOOLEFORCE_LOG
  if (verbose >= 2)
    fprintf (output,
	     "c extracted %d core variables (%.0f%% out of %d)\n",
	     count, PERCENT (count, max_variable_idx), max_variable_idx);
#endif

  vars_core_generated = 1;
}

/*------------------------------------------------------------------------*/

int
booleforce_var_in_core (int idx)
{
  int res;
  booleforce_enter ();
  if (!vars_core_generated)
    extract_vars_in_core ();
  res = idx2var (idx)->core != 0;
  booleforce_leave ();
  return res;
}

/*------------------------------------------------------------------------*/

int
booleforce_print_variable_core (FILE * file)
{
  double start_time;
  int i, res;

  booleforce_enter ();

  extract_clausal_core ();

  start_time = booleforce_time_stamp ();
  if (verbose >= 2)
    fprintf (output,
	     "c printing variable core with maximal variable index %d\n",
	     max_variable_idx);

  res = 0;
  for (i = 1; i <= max_variable_idx; i++)
    {
      if (!booleforce_var_in_core (i))
	continue;
      fprintf (file, "%d\n", i);
      res++;
    }
  booleforce_leave ();

  if (verbose >= 1)
    booleforce_report (start_time, output,
		       "c printed variable core of %d variables (%.1f%%)",
		       res, PERCENT (res, max_variable_idx));

  return res;
}

/*------------------------------------------------------------------------*/

int
booleforce_print_clausal_core (FILE * file)
{
  double start_time;
  Clause ** p, * clause;
  int res, count;

  booleforce_enter ();

  extract_clausal_core ();

  start_time = booleforce_time_stamp ();
  if (verbose >= 2)
    fprintf (output, "c printing clausal core of original clauses\n");

  count = res = 0;

  for (p = clauses.start; p < clauses.last; p++)
    {
      clause = *p;
      if (!clause || !clause->original)
	continue;

      count++;
      if (clause->core)
	res++;
    }

  fprintf (file, "p cnf %d %d\n", max_variable_idx, res);

  for (p = clauses.start; p < clauses.last; p++)
    {
      clause = *p;
      if (!clause || !clause->original || !clause->core)
	continue;

      print_clause (file, clause);
    }

  if (verbose >= 1)
    booleforce_report (start_time, output,
		       "c printed clausal core of %d clauses (%.1f%%)", 
		       res, PERCENT (res, count));

  return res;
}

/*------------------------------------------------------------------------*/
#else /* #undef BOOLEFORCE_TRACE */
/*------------------------------------------------------------------------*/

void
booleforce_print_resolution_trace (FILE * file, int extended)
{
  (void) extended;
  booleforce_enter ();
  fputs ("libboolefoce: printing of resolution trace not supported\n", file);
  booleforce_leave ();
}

/*------------------------------------------------------------------------*/

int
booleforce_var_in_core (int idx)
{
  (void) idx;
  /* silently assume that all variables are in core */
  return 1;			
}

/*------------------------------------------------------------------------*/

int
booleforce_print_variable_core (FILE * file)
{
  booleforce_enter ();
  fputs ("libboolefoce: printing of variable core not supported\n", file);
  booleforce_leave ();
  return -1;
}

/*------------------------------------------------------------------------*/

int
booleforce_print_clausal_core (FILE * file)
{
  booleforce_enter ();
  fputs ("libboolefoce: printing of clausal core not supported\n", file);
  booleforce_leave ();
  return -1;
}

/*------------------------------------------------------------------------*/
#endif
/*------------------------------------------------------------------------*/

double
booleforce_seconds (void)
{
  double res;
  booleforce_enter ();
  res = adjusted_seconds ();
  booleforce_leave ();
  return res;
}

/*------------------------------------------------------------------------*/

void
booleforce_resources (FILE * file)
{
  booleforce_enter ();
  fprintf (file, "c allocated maximum %.1f MB\n", max_mega_bytes ());
  fprintf (file, "c %.2f seconds\n", booleforce_seconds ());
  booleforce_leave ();
}

/*------------------------------------------------------------------------*/
#ifdef BOOLEFORCE_STATS
/*------------------------------------------------------------------------*/

#define FMT64 INT64FMT

#define EXTENDED_HRULE \
"c+----------+----------+----------+----------+--------+-----------+--------+\n"

#define EXTENDED_CLAUSE_STATS_LINE_FMT(str) \
"c| " str  " |%9d"    " |%9d"    " |%9d"   " |%7d"  " |%10"FMT64" |%7.1f"" |\n"

#define EXTENDED_CLAUSE_STATS_LINE_ARGS(type,dynamic) \
  stats.type.dynamic.clauses, \
    stats.type.dynamic.large, \
    stats.type.dynamic.binary, \
    stats.type.dynamic.unary, \
    stats.type.dynamic.literals, \
    AVG (stats.type.dynamic.literals, stats.type.dynamic.clauses)

#define EXTENDED_CLAUSE_STATS_LINE(type) \
do { \
  fprintf (file, \
EXTENDED_CLAUSE_STATS_LINE_FMT("%8s") \
EXTENDED_CLAUSE_STATS_LINE_FMT("   added") \
EXTENDED_CLAUSE_STATS_LINE_FMT(" removed") \
EXTENDED_CLAUSE_STATS_LINE_FMT("     max") \
EXTENDED_HRULE \
, \
  # type , \
  EXTENDED_CLAUSE_STATS_LINE_ARGS(type,current), \
  EXTENDED_CLAUSE_STATS_LINE_ARGS(type,added), \
  EXTENDED_CLAUSE_STATS_LINE_ARGS(type,removed), \
  EXTENDED_CLAUSE_STATS_LINE_ARGS(type,max)); \
} while(0)

/*------------------------------------------------------------------------*/

static void
extended_stats (FILE * file)
{
/**INDENT-OFF**/
  fprintf (file, 
    EXTENDED_HRULE
"c|          |  clauses |    large |   binary |  unary |  literals | length |\n"
    EXTENDED_HRULE);

  EXTENDED_CLAUSE_STATS_LINE (original);
  EXTENDED_CLAUSE_STATS_LINE (learned);
  EXTENDED_CLAUSE_STATS_LINE (resolved);
  EXTENDED_CLAUSE_STATS_LINE (all);

  fprintf (file, 
"c %d iterations with %d top level assignments\n",
  stats.iterations, top_level_assigned);

  fprintf (file,
"c reduced %"INT64FMT" literals of %"INT64FMT" clauses in %d reductions\n",
  stats.reduced_learned_literals,
  stats.reduced_learned_clauses, 
  stats.reduce_learned_clauses_gcs);

  fprintf (file,
"c %d restarts and %.1f average conflict height\n",
  stats.restarts, avg_height ());

  fprintf (file,
"c %d failed literals in %d rounds produced %d assignments\n"
,
  stats.failed_literals, 
    stats.failed_literal_rounds, 
    stats.assignments_through_failed_literals);

  fprintf (file,
"c %d decisions with %"FMT64" pops (%.1f/decision)\n"
,
  stats.decisions,
    stats.pops,
    AVG (stats.pops, stats.decisions));

  fprintf (file,
"c %d random decisions (%.1f%%)\n",
    stats.random_decisions,
    PERCENT (stats.random_decisions, stats.decisions));

  /* TODO: add 'conflicts' if multiple conflicts can be generated */
  assert (stats.backtracks == stats.conflicts);

  fprintf (file,
"c %d small decisions only clauses (%.1f%%) of average length %.1f\n"
,
  stats.small_decision_clauses,
    PERCENT (stats.small_decision_clauses, stats.learned.added.clauses),
    AVG (stats.small_decision_clauses_sum, stats.small_decision_clauses));

  fprintf (file,
"c %"FMT64" backtracks with %"FMT64
" pushs (%.1f/backtrack) and %d uips (%.0f%%)\n"
"c %"FMT64" backjumps (%.0f%%) over %"FMT64" levels (%.1f/backjump)\n"
,
  stats.backtracks,
    stats.pushs, AVG (stats.pushs, stats.backtracks), stats.uips,
    PERCENT (stats.uips, stats.backtracks),
  stats.backjumps, PERCENT (stats.backjumps, stats.backtracks),
    stats.backjumpedlevels, AVG (stats.backjumpedlevels, stats.backjumps));

  fprintf (file,
"c %"FMT64" resolved premisses (%.1f/reason %.1f/conflict)\n"
"c %"FMT64" resolved reasons in implication chains (%.1f/conflict)\n"
"c %"FMT64" resolved conflicts with implication chains (%.1f%%)\n"
,
  stats.resolved_premisses, 
    AVG (stats.resolved_premisses, stats.resolved_implications),
    AVG (stats.resolved_premisses, stats.resolved_implication_chains),
  stats.resolved_implications,
    AVG (stats.resolved_implications, stats.resolved_implication_chains),
  stats.resolved_implication_chains,
    PERCENT (stats.resolved_implication_chains, stats.conflicts));
  
  assert (stats.unshrunken_literals >= stats.shrunken_literals);
  fprintf (file,
"c %"FMT64" shrunken learned clauses (%.1f%%)\n"
"c %"FMT64" shrunken literals (%.1f/shrunken %.1f/learned)\n"
"c shrinking learned clauses with %.1f%% compression rate\n"
,
  stats.shrunken_clauses, 
    PERCENT (stats.shrunken_clauses, stats.learned.added.clauses),
  stats.shrunken_literals,
    AVG (stats.shrunken_literals, stats.shrunken_clauses),
    AVG (stats.shrunken_literals, stats.learned.added.clauses),
    PERCENT (stats.shrunken_literals, stats.unshrunken_literals));

  fprintf (file,
"c %d rescaled variables (%.1f/backtrack) current increment ",
  stats.variable_rescales,
    AVG (stats.variable_rescales, stats.backtracks));
  booleforce_print_uwe (var_score_inc, output);
  fputc ('\n', output);

  fprintf (file,
"c %d rescaled clauses (%.1f/backtrack) current increment ",
  stats.clause_rescales,
    AVG (stats.clause_rescales, stats.backtracks));
  booleforce_print_uwe (clause_score_inc, output);
  fputc ('\n', output);

  fprintf (file,
"c %"FMT64" swapped ranks (%.1f/push %.1f/pop %.1f/inc)\n",
  stats.swaps,
    AVG (stats.swaps_per_push, stats.pushs),
    AVG (stats.swaps_per_pop, stats.pops),
    AVG (stats.swaps_per_var_score_inc, stats.var_score_incs));

  fprintf (file,
"c %"FMT64" bcps propagating %"FMT64" assignments (%.1f/propagation)\n"
,
  stats.bcps, stats.propagations, 
    AVG (stats.propagations, stats.bcps));

  fprintf (file,
"c %"FMT64" propagations (%.1f/decision %.1f/bcp %.1f/assignment)\n"
,
  stats.propagations,
  AVG (stats.propagations, stats.decisions),
  AVG (stats.propagations, stats.bcps),
  AVG (stats.propagations, stats.assignments));

  fprintf (file,
"c traversed %"FMT64" literals in %"FMT64" visited clauses\n"
"c %.1f traversals/visit %"FMT64" satisfied watched literals (%.0f%%)\n"
,
  stats.traversals, stats.visits, 
  AVG (stats.traversals, stats.visits), stats.other_watched_true, 
    PERCENT (stats.other_watched_true, stats.visits));

  fprintf (file,
"c %"FMT64" antecedents (%.1f/learned)\n"
,
    stats.antecedents, AVG (stats.antecedents, stats.learned.added.clauses));

  fprintf (file,
"c %d full and %d fast garbage collections at top level\n",
  stats.full_top_level_gcs, stats.fast_top_level_gcs);

  fprintf (file,
"c recycled %"FMT64" literals in %"FMT64" clauses\n",
  stats.recycled_literals, stats.recycled_clauses);

  fprintf (file,
"c recycled %.1f MB in %.2f seconds\n",
  stats.recycled_bytes / (double)(1<<20),
  stats.gc_time);

/**INDENT-ON**/
}

/*------------------------------------------------------------------------*/
#endif
/*------------------------------------------------------------------------*/

void
booleforce_stats (FILE * file)
{
  booleforce_enter ();

#ifdef BOOLEFORCE_STATS
  extended_stats (file);
#endif
  booleforce_resources (file);
  fflush (file);

  booleforce_leave ();
}

/*------------------------------------------------------------------------*/

const char *
booleforce_configuration (void)
{
  return
    "VERSION=\"" BOOLEFORCE_VERSION "\"\n"
    "OS=\"" BOOLEFORCE_OS "\"\n"
    "ID=\"$Id: booleforce.c,v 1.261 2009-06-19 09:44:28 biere Exp $\"\n"
    "CC=\"" BOOLEFORCE_CC "\"\n"
    "CCVERSION=\"" BOOLEFORCE_CCVERSION "\"\n"
    "CFLAGS=\"" BOOLEFORCE_CFLAGS "\"\n"
#ifdef NDEBUG
    "NDEBUG=1\n"
#else
    "NDEBUG=0\n"
#endif
#ifdef BOOLEFORCE_STATS
    "BOOLEFORCE_STATS=1\n"
#else
    "BOOLEFORCE_STATS=0\n"
#endif
#ifdef BOOLEFORCE_LOG
    "LOG=1\n"
#else
    "LOG=0\n"
#endif
#ifdef BOOLEFORCE_TRACE
    "BOOLEFORCE_TRACE=1\n"
#else
    "BOOLEFORCE_TRACE=0\n"
#endif
    ;
}

/*------------------------------------------------------------------------*/

const char *
booleforce_id (void)
{
  return "$Id: booleforce.c,v 1.261 2009-06-19 09:44:28 biere Exp $";
}

/*------------------------------------------------------------------------*/

const char *
booleforce_version (void)
{
  return BOOLEFORCE_VERSION;
}
