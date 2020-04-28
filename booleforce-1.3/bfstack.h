/*------------------------------------------------------------------------*/
/* Copyright (c) 2005 - 2010 Armin Biere, Johannes Kepler University.     */
/*------------------------------------------------------------------------*/

#ifndef BOOLEFORCE_stack_h_INCLUDED
#define BOOLEFORCE_stack_h_INCLUDED

/*------------------------------------------------------------------------*/

#define PtrStack(Type) Type ## PtrStack

#define DeclarePtrStack(Type) \
typedef struct PtrStack(Type) PtrStack(Type); \
\
struct PtrStack(Type) \
{ \
  Type ** start; \
  Type ** last; \
  Type ** end; \
};

/*------------------------------------------------------------------------*/

#define Stack(Type) Type ## Stack

#define DeclareStack(Type) \
typedef struct Stack(Type) Stack(Type); \
\
struct Stack(Type) \
{ \
  Type * start; \
  Type * last; \
  Type * end; \
};
/*------------------------------------------------------------------------*/

DeclareStack (char);
DeclareStack (int);
DeclareStack (unsigned);

/*------------------------------------------------------------------------*/

#define count_stack(stack) \
  ((int)((stack).last - (stack).start))

/*------------------------------------------------------------------------*/

#define size_stack(stack) \
  ((stack).end - (stack).start)

/*------------------------------------------------------------------------*/

#define empty_stack(stack) \
  ((stack).last == (stack).start)

/*------------------------------------------------------------------------*/

#define full_stack(stack) \
  ((stack).last == (stack).end)

/*------------------------------------------------------------------------*/

#define bytes_stack(stack) \
  (sizeof((stack).start[0]) * size_stack(stack))

/*------------------------------------------------------------------------*/

#define enlarge_stack(stack) \
do { \
  int old_size = size_stack(stack); \
  int new_size = old_size ? 2 * old_size : 2; \
  size_t old_bytes = old_size * sizeof ((stack).start[0]); \
  size_t new_bytes = new_size * sizeof ((stack).start[0]); \
  (stack).start = booleforce_enlarge ((stack).start, old_bytes, new_bytes); \
  (stack).last = (stack).start + old_size; \
  (stack).end = (stack).start + new_size; \
} while(0)

/*------------------------------------------------------------------------*/

#define push_stack(stack,data) \
do { \
  if (full_stack (stack)) \
    enlarge_stack (stack); \
  *(stack).last++ = (data); \
} while(0)

/*------------------------------------------------------------------------*/

#define pop_stack(stack) \
  (assert (count_stack (stack)),*--(stack).last)

/*------------------------------------------------------------------------*/

#define top_stack(stack) \
  (assert (count_stack (stack)),(stack).last[-1])

/*------------------------------------------------------------------------*/

#define init_stack(stack) \
  do { \
    (stack).start = 0; \
    (stack).last = 0; \
    (stack).end = 0; \
  } while (0)

/*------------------------------------------------------------------------*/

#define release_stack(stack) \
  do { \
    booleforce_delete ((stack).start, bytes_stack (stack)); \
    init_stack (stack); \
  } while(0)

/*------------------------------------------------------------------------*/

#define DELETE_STACK(stack) \
  do { \
    assert (stack); \
    release_stack (*(stack)); \
    booleforce_delete (stack, sizeof (*(stack))); \
  } while(0)

/*------------------------------------------------------------------------*/

#define reset_stack(stack,new_count) \
  do { \
    assert (0 <= (new_count)); \
    assert (new_count <= count_stack (stack)); \
    (stack).last = (stack).start + (new_count); \
  } while(0)

/*------------------------------------------------------------------------*/

#define forall_stack(stack,it) \
  for (it = (stack).start; it != (stack).last; it++)

/*------------------------------------------------------------------------*/

#define stack2ints(stack) \
  booleforce_intcpy ((stack).start, count_stack (stack))

/*------------------------------------------------------------------------*/

#define stack2unsigneds(s) \
  (unsigned*) booleforce_intcpy ((int*)((s).start), count_stack (s))

/*------------------------------------------------------------------------*/
#endif
