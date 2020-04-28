/*------------------------------------------------------------------------*/
/* Copyright (c) 2005 - 2010 Armin Biere, Johannes Kepler University.     */
/*------------------------------------------------------------------------*/

#include "config.h"

/*------------------------------------------------------------------------*/

#include <assert.h>
#include <stdio.h>
#include <string.h>

/*------------------------------------------------------------------------*/

FILE * fopen64 (const char *, const char *);

/*------------------------------------------------------------------------*/

#include "bfio.h"
#include "bfmem.h"
#include "bfstack.h"

/*------------------------------------------------------------------------*/

#define GUNZIP_FMT "gunzip -c %s"
#define GZIP_FMT "gzip -c > %s"

/*------------------------------------------------------------------------*/

typedef struct InternalFile InternalFile;

/*------------------------------------------------------------------------*/

struct InternalFile
{
  char *name;
  int pos;
  FILE *file;
  int zipped;
};

/*------------------------------------------------------------------------*/

DeclarePtrStack (InternalFile);

/*------------------------------------------------------------------------*/

static InternalFilePtrStack files;

/*------------------------------------------------------------------------*/

static int
has_gz_suffix (const char *name)
{
  int len;
  assert (name);

  len = strlen (name);
  if (len < 3)
    return 0;

  if (name[len - 3] != '.')
    return 0;

  if (name[len - 2] != 'g')
    return 0;

  if (name[len - 1] != 'z')
    return 0;

  return 1;
}

/*------------------------------------------------------------------------*/

static InternalFile *
find_file (FILE * file)
{
  InternalFile *internal_file;
  int i;

  for (i = 0; i < count_stack (files); i++)
    {
      internal_file = files.start[i];
      assert (internal_file);
      if (internal_file->file == file)
	return internal_file;
    }

  return 0;
}

/*------------------------------------------------------------------------*/

static void
new_file (const char *name, FILE * file)
{
  InternalFile *res;

  assert (!find_file (file));

  BOOLEFORCE_NEW (res);
  res->name = booleforce_strdup (name);
  res->file = file;
  res->zipped = has_gz_suffix (name);
  res->pos = count_stack (files);
  push_stack (files, res);
  assert (files.start[res->pos] == res);
}

/*------------------------------------------------------------------------*/

static void
delete_file (InternalFile * internal_file)
{
  InternalFile *last;

  assert (internal_file);
  assert (files.start[internal_file->pos] == internal_file);

  last = pop_stack (files);
  if (last != internal_file)
    {
      assert (0 <= internal_file->pos);
      assert (0 < count_stack (files));
      files.start[internal_file->pos] = last;
      last->pos = internal_file->pos;
    }

  if (internal_file->zipped)
    pclose (internal_file->file);
  else
    fclose (internal_file->file);

  booleforce_delstr (internal_file->name);
  BOOLEFORCE_DELETE (internal_file);

  if (empty_stack (files))
    release_stack (files);
}

/*------------------------------------------------------------------------*/

static FILE *
popen_gzipped_file_for_reading (const char *file_name)
{
  size_t bytes;
  char *cmd;
  FILE *res;

  bytes = strlen (GUNZIP_FMT) - 2 + strlen (file_name) + 1;
  cmd = booleforce_new (bytes);
  sprintf (cmd, GUNZIP_FMT, file_name);
  res = popen (cmd, "r");
  booleforce_delete (cmd, bytes);

  return res;
}

/*------------------------------------------------------------------------*/

FILE *
booleforce_open_file_for_reading (const char *name)
{
  FILE *res;

  if (has_gz_suffix (name)) {
    res = popen_gzipped_file_for_reading (name);
  } else {
#ifndef FOPEN64_FOPEN
    res = fopen64 (name, "r");
#else
	  res = fopen(name, "r");
#endif
	}

  if (res)
    new_file (name, res);

  return res;
}

/*------------------------------------------------------------------------*/

static FILE *
popen_gzipped_file_for_writing (const char * file_name)
{
  size_t bytes;
  char *cmd;
  FILE *res;

  bytes = strlen (GZIP_FMT) - 2 + strlen (file_name) + 1;
  cmd = booleforce_new (bytes);
  sprintf (cmd, GZIP_FMT, file_name);
  res = popen (cmd, "w");
  booleforce_delete (cmd, bytes);

  return res;
}

/*------------------------------------------------------------------------*/

FILE *
booleforce_open_file_for_writing (const char * name)
{
  FILE * res;

  if (has_gz_suffix (name))
    res = popen_gzipped_file_for_writing (name);
  else
    res = fopen (name, "w");

  if (res)
    new_file (name, res);

  return res;
}

/*------------------------------------------------------------------------*/

void
booleforce_close_file (FILE * file)
{
  InternalFile *internal_file;
  assert (file);
  internal_file = find_file (file);
  assert (internal_file);
  delete_file (internal_file);
}

/*------------------------------------------------------------------------*/

int
booleforce_fill_buffer (BooleforceInputBuffer * buffer)
{
  size_t bytes;

  assert (buffer->next == buffer->end);

  if (feof (buffer->file))	/* necessary for <stdin> */
    bytes = 0;
  else
    bytes = fread (buffer->start, 1, BOOLEFORCE_BUFFER_SIZE, buffer->file);

  if (!bytes)
    return EOF;

  buffer->end = buffer->start + bytes;
  buffer->next = buffer->start;

  return *buffer->next++;
}
