/*------------------------------------------------------------------------*/
/* Copyright (C) 2014-2014, Armin Biere, Johannes Kepler University, Linz */
/*------------------------------------------------------------------------*/

#include "druplig.h"

#include <assert.h>
#include <limits.h>
#include <stdio.h>
#include <string.h>
#include <unistd.h>

/*------------------------------------------------------------------------*/

static Druplig * druplig;
static FILE * file;

/*------------------------------------------------------------------------*/

static void init (const char * name) {
  char buffer[80];
  sprintf (buffer, "log/%s.log", name);
  file = fopen (buffer, "w");
  druplig = druplig_init ();
  druplig_set_check (druplig, 1);
  druplig_set_trace (druplig, file);
  druplig_set_traceorig (druplig, 1);
  druplig_banner (file);
  druplig_options (druplig, file);
}

static void reset () {
  druplig_stats (druplig, file);
  druplig_reset (druplig);
  fclose (file);
}

/*------------------------------------------------------------------------*/

#define INIT() init (__FUNCTION__)
#define RESET reset

#define ORIG0() \
do { \
  druplig_add_original_clause (druplig); \
} while (0)

#define ORIG1(A) \
do { \
  druplig_add_literal (druplig, (A)); \
  druplig_add_original_clause (druplig); \
} while (0)

#define ORIG2(A,B) \
do { \
  druplig_add_literal (druplig, (A)); \
  druplig_add_literal (druplig, (B)); \
  druplig_add_original_clause (druplig); \
} while (0)

#define ORIG3(A,B,C) \
do { \
  druplig_add_literal (druplig, (A)); \
  druplig_add_literal (druplig, (B)); \
  druplig_add_literal (druplig, (C)); \
  druplig_add_original_clause (druplig); \
} while (0)

#define ORIG4(A,B,C,D) \
do { \
  druplig_add_literal (druplig, (A)); \
  druplig_add_literal (druplig, (B)); \
  druplig_add_literal (druplig, (C)); \
  druplig_add_literal (druplig, (D)); \
  druplig_add_original_clause (druplig); \
} while (0)

#define ORIG5(A,B,C,D,E) \
do { \
  druplig_add_literal (druplig, (A)); \
  druplig_add_literal (druplig, (B)); \
  druplig_add_literal (druplig, (C)); \
  druplig_add_literal (druplig, (D)); \
  druplig_add_literal (druplig, (E)); \
  druplig_add_original_clause (druplig); \
} while (0)

/*------------------------------------------------------------------------*/

#define RED0(A) \
do { \
  druplig_check_and_add_redundant_clause (druplig); \
} while (0)

#define RED1(A) \
do { \
  druplig_add_literal (druplig, (A)); \
  druplig_check_and_add_redundant_clause (druplig); \
} while (0)

#define RED2(A,B) \
do { \
  druplig_add_literal (druplig, (A)); \
  druplig_add_literal (druplig, (B)); \
  druplig_check_and_add_redundant_clause (druplig); \
} while (0)

#define RED3(A,B,C) \
do { \
  druplig_add_literal (druplig, (A)); \
  druplig_add_literal (druplig, (B)); \
  druplig_add_literal (druplig, (C)); \
  druplig_check_and_add_redundant_clause (druplig); \
} while (0)

/*------------------------------------------------------------------------*/

#define NORED1(A) \
do { \
  int res; \
  druplig_add_literal (druplig, (A)); \
  druplig_set_die (druplig, 0); \
  res = druplig_check_and_add_redundant_clause (druplig); \
  if (res) abort (); \
  druplig_set_die (druplig, 1); \
} while (0)

#define NORED2(A,B) \
do { \
  int res; \
  druplig_add_literal (druplig, (A)); \
  druplig_add_literal (druplig, (B)); \
  druplig_set_die (druplig, 0); \
  res = druplig_check_and_add_redundant_clause (druplig); \
  if (res) abort (); \
  druplig_set_die (druplig, 1); \
} while (0)

/*------------------------------------------------------------------------*/

#define DEL0(A) \
do { \
  druplig_forget_clause (druplig); \
} while (0)

#define DEL1(A) \
do { \
  druplig_add_literal (druplig, (A)); \
  druplig_forget_clause (druplig); \
} while (0)

#define DEL2(A,B) \
do { \
  druplig_add_literal (druplig, (A)); \
  druplig_add_literal (druplig, (B)); \
  druplig_forget_clause (druplig); \
} while (0)

#define DEL3(A,B,C) \
do { \
  druplig_add_literal (druplig, (A)); \
  druplig_add_literal (druplig, (B)); \
  druplig_add_literal (druplig, (C)); \
  druplig_forget_clause (druplig); \
} while (0)

#define DEL4(A,B,C,D) \
do { \
  druplig_add_literal (druplig, (A)); \
  druplig_add_literal (druplig, (B)); \
  druplig_add_literal (druplig, (C)); \
  druplig_add_literal (druplig, (D)); \
  druplig_forget_clause (druplig); \
} while (0)

/*------------------------------------------------------------------------*/

#define NODEL0(A) \
do { \
  int res; \
  druplig_set_die (druplig, 0); \
  res = druplig_forget_clause (druplig); \
  if (res) abort (); \
  druplig_set_die (druplig, 1); \
} while (0)

#define NODEL1(A) \
do { \
  int res; \
  druplig_add_literal (druplig, (A)); \
  druplig_set_die (druplig, 0); \
  res = druplig_forget_clause (druplig); \
  if (res) abort (); \
  druplig_set_die (druplig, 1); \
} while (0)

#define NODEL2(A,B) \
do { \
  int res; \
  druplig_add_literal (druplig, (A)); \
  druplig_add_literal (druplig, (B)); \
  druplig_set_die (druplig, 0); \
  res = druplig_forget_clause (druplig); \
  if (res) abort (); \
  druplig_set_die (druplig, 1); \
} while (0)

#define NODEL3(A,B,C) \
do { \
  int res; \
  druplig_add_literal (druplig, (A)); \
  druplig_add_literal (druplig, (B)); \
  druplig_add_literal (druplig, (C)); \
  druplig_set_die (druplig, 0); \
  res = druplig_forget_clause (druplig); \
  if (res) abort (); \
  druplig_set_die (druplig, 1); \
} while (0)

/*------------------------------------------------------------------------*/

static void test000 () {
  INIT ();
  RESET ();
}

static void test001 () {
  INIT ();
  ORIG2 (1, -2);
  ORIG2 (2, -1);
  druplig_add_original_clause (druplig);
  RESET ();
}

static void test002 () {
  INIT ();
  RED2 (1, -1);
  RED2 (2, -2);
  RED2 (3, -3);
  RESET ();
}

static void test003 () {
  INIT ();
  ORIG1 (1);
  ORIG2 (-1, 2);
  ORIG2 (-1, -3);
  RED1 (2);
  RED1 (-3);
  RESET ();
}

static void test004 () {
  INIT ();
  ORIG3 (1, 2, 3);
  ORIG3 (1, 2, -3);
  RED2 (1, 2);
  ORIG3 (-1, 2, -3);
  RED2 (-3, 2);
  RESET ();
}

static void test005 () {
  INIT ();
  ORIG1 (1);
  ORIG1 (-1);
  RED0 ();
  RESET ();
}

static void test006 () {
  INIT ();
  ORIG2 (1, 2);
  ORIG2 (1, -2);
  ORIG2 (-1, 2);
  ORIG2 (-1, -2);
  RED1 (2);
  RED1 (1);
  RED1 (-2);
  RED0 ();
  RESET ();
}

static void test007 () {
  INIT ();
  ORIG1 (1);
  ORIG2 (-1, 2);
  ORIG3 (-1, -2, 3);
  ORIG5 (-1, -2, -3, 4, 5);
  RED3 (4, 5, 6);
  RESET ();
}

static void test008 () {
  INIT ();
  ORIG2 (-1, 5);
  ORIG2 (-4, 3);
  ORIG2 (-2, 6);
  ORIG1 (2);
  ORIG1 (-3);
  ORIG4 (4, -6, -7, 1);
  RED2  (5, -7);
  RESET ();
}

static void test009 () {
  INIT ();
  ORIG2 (-1, 2);
  ORIG2 (1, 2);
  RED1 (2);
  NORED1 (1);
  RESET ();
}

static void test010 () {
  INIT ();
  ORIG2 (2, -4);
  ORIG2 (-2, -4);
  ORIG4 (1, 2, 3, 4);
  RED1 (-4);
  RED3 (1, 2, 3);
  NORED2 (2, 3);
  RESET ();
}

static void test011 () {
  INIT ();
  ORIG1 (-4);
  ORIG2 (-1, 2);
  ORIG2 (2, 3);
  RED3 (-1, 2, 3);
  DEL2 (3, 2);
  DEL2 (2, -1);
  DEL3 (-1, 2, 3);
  ORIG1 (4);
  DEL1 (-4);
  RED0 ();
  RESET ();
}

static void test012 () {
  INIT ();
  ORIG2 (1, -2);
  NODEL2 (1, 2);
  NODEL2 (-1, 2);
  ORIG2 (-2, 3);
  NODEL2 (2, 3);
  NODEL2 (2, -3);
  RED3 (1, -2, 3);
  NODEL3 (1, 2, 3);
  NODEL3 (-1, 2, 3);
  NODEL3 (-1, 2, -3);
  NODEL3 (1, 2, -3);
  NODEL2 (1, 4);
  DEL2 (3, -2);
  NODEL2 (-2, 3);
  DEL2 (-2, 1);
  DEL3 (1, -2, 3);
  NODEL3 (1, -2, 3);
  NODEL2 (1, -2);
  RESET ();
}

static void test013 () {
  INIT ();
  ORIG4 (7, 2, 6, -5);
  ORIG1 (-7);
  ORIG1 (-6);
  ORIG4 (3, -2, 4, 1);
  ORIG1 (5);
  RED1 (2);
  DEL4 (7, 2, 6, -5);
  RED3 (3, 4, 1);
  RESET ();
}

static void test014 () {
  INIT ();
  ORIG0 ();
  ORIG0 ();
  DEL0 ();
  DEL0 ();
  NODEL0 ();
  RESET ();
}

/*------------------------------------------------------------------------*/

#define CR() \
do { \
  if (isatty (1)) fputc ('\r', stdout); \
} while (0)

#define NL() \
do { \
  if (!isatty (1)) fputc ('\n', stdout); \
} while (0)

#define TEST(NAME) \
do { \
  int i = 0; \
  if (argc > 1) \
    for (i = 1; i < argc; i++) \
      if (!strcmp (argv[i], #NAME)) \
	break; \
  if (i >= argc) break; \
  CR (); \
  printf ("%s ", #NAME); \
  fflush (stdout); \
  NAME (); \
  executed++; \
  NL (); \
} while (0)

int main (int argc, char ** argv) {
  int executed = 0;
  TEST (test000);
  TEST (test001);
  TEST (test002);
  TEST (test003);
  TEST (test004);
  TEST (test005);
  TEST (test006);
  TEST (test007);
  TEST (test008);
  TEST (test009);
  TEST (test010);
  TEST (test011);
  TEST (test012);
  TEST (test013);
  TEST (test014);
  CR ();
  printf ("executed %d tests succesfully.\n", executed);
  return 0;
}
