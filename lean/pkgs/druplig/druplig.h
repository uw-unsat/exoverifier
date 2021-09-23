/*------------------------------------------------------------------------*/
/* Copyright (C) 2014-2014, Armin Biere, Johannes Kepler University, Linz */
/*------------------------------------------------------------------------*/

#ifndef DRUPLIG_INCLUDED
#define DRUPLIG_INCLUDED

#include <stdio.h>
#include <stdlib.h>

typedef struct Druplig Druplig;

/*------------------------------------------------------------------------*/

typedef void * (*druplig_malloc) (void*mem, size_t);
typedef void (*druplig_free) (void*mem, void*, size_t);
typedef void * (*druplig_realloc) (void*mem, void *ptr, size_t old, size_t);

Druplig * druplig_minit (void *mem,
            druplig_malloc, druplig_realloc, druplig_free);

/*------------------------------------------------------------------------*/

Druplig * druplig_init ();
void druplig_reset (Druplig *);

/*------------------------------------------------------------------------*/

void druplig_set_check (Druplig *, int check);
void druplig_set_flush (Druplig *, int flush);
void druplig_set_trace (Druplig *, FILE *);
void druplig_set_traceorig (Druplig *, int);
void druplig_set_die (Druplig *, int);

/*------------------------------------------------------------------------*/

void druplig_banner (FILE *);
void druplig_options (Druplig *, FILE *);
void druplig_stats (Druplig *, FILE *);

/*------------------------------------------------------------------------*/

void druplig_add_literal (Druplig *, int);
void druplig_add_literals (Druplig *, int *);
void druplig_add_literal_args (Druplig *, ...);

void druplig_add_original_clause (Druplig *);
int druplig_check_and_add_redundant_clause (Druplig *);
int druplig_forget_clause (Druplig *);

/*------------------------------------------------------------------------*/

#endif
