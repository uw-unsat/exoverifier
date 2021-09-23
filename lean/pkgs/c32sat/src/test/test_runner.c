/*
 Institute for Formal Models and Verification (FMV),
 Johannes Kepler University Linz, Austria
 
 Copyright (c) 2006, Robert Daniel Brummayer
 All rights reserved.

 Redistribution and use in source and binary forms, with or without
 modification, are permitted provided that the following conditions are met:

    * Redistributions of source code must retain the above copyright notice,
      this list of conditions and the following disclaimer.
    * Redistributions in binary form must reproduce the above copyright notice,
      this list of conditions and the following disclaimer in the documentation
      and/or other materials provided with the distribution.
    * Neither the name of the FMV nor the names of its contributors may be
      used to endorse or promote products derived from this software without
      specific prior written permission.

 THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
 AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
 DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER OR CONTRIBUTORS BE LIABLE
 FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
 SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
 CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
 OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */
#include <assert.h>
#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include "test_logging.h"
#include "random_utilities.h"
#include "c32sat_math_test.h"
#include "memory_management_test.h"
#include "token_test.h"
#include "symbol_test.h"
#include "error_management_test.h"
#include "scanner_test.h"
#include "parser_test.h"
#include "parse_tree_test.h"
#include "parse_tree_analysis_test.h"
#include "app_test.h"
#include "aig_test.h"
#include "aig_vector_test.h"
#include "aig_transformation_test.h"
#include "linked_list_test.h"
#include "hash_table_test.h"
#include "parse_tree_transformation_test.h"
#include "sat_solver_test.h"
#include "cnf_test.h"
#include "stack_test.h"
#include "aig_id_generation_test.h"
#include "aig_2_cnf_transformation_standard_tseitin_test.h"
#include "../config.h"

static const char *option_no_bash = "-no-bash-colors";
static const char *msg_usage = "Usage: test [-no-bash-colors]";
static const char *bash_green = "\e[1;32m";
static const char *bash_red = "\e[1;31m";
static const char *bash_default = "\e[0;39m";

/** Runs all test cases. */
void
run_all_tests (int bash)
{
  assert (sizeof (int) >= 4);
  assert (sizeof (long int) == sizeof (void *));
  assert (sizeof (long long int) >= 8);
  assert (ext_number_of_bits == 32);
  init_test_logging (bash);
  init_random_utilites ();
  printf ("\nRunning C32SAT tests:\n\n");
  printf ("\nRunning error management test(s):\n");
  run_error_management_tests ();
  printf ("Running memory management test(s):\n");
  run_memory_management_tests ();  
  printf ("\nRunning C32SAT math test(s):\n");
  run_c32sat_math_tests ();
  printf ("Running stack test(s):\n");
  run_stack_tests ();
  printf ("Running linked list test(s):\n");
  run_linked_list_tests ();
  printf ("\nRunning cnf test(s):\n");
  run_cnf_tests ();
  printf ("\nRunning sat solver test(s):\n");
  run_sat_solver_tests ();
  printf ("\nRunning hash table test(s):\n");
  run_hash_table_tests ();
  printf ("\nRunning symbol test(s):\n");
  run_symbol_tests ();
  printf ("\nRunning token test(s):\n");
  run_token_tests ();
  printf ("\nRunning scanner test(s):\n");
  run_scanner_tests ();
  printf ("\nRunning parser test(s):\n");
  run_parser_tests ();
  printf ("\nRunning parse tree test(s):\n");
  run_parse_tree_tests ();
  printf ("\nRunning parse tree analysis test(s):\n");
  run_parse_tree_analysis_tests ();
  printf ("\nRunning AIG test(s):\n");
  run_aig_tests ();
  printf ("\nRunning AIG id generation test(s):\n");
  run_aig_id_generation_tests ();
  printf ("\nRunning AIG vector test(s) for 32 bits:\n");
  run_aig_vector_tests ();
  printf ("\nRunning AIG transformation test(s):\n");
  run_aig_transformation_tests ();
  printf ("\nRunning AIG to CNF transformation standard tseitin test(s):\n");
  run_aig_2_cnf_transformation_standard_tseitin_tests ();
  printf ("\nRunning parse tree transformation test(s):\n");
  run_parse_tree_transformation_tests ();
  printf ("\nRunning application test(s):\n");
  run_app_tests ();
  if (bash)
    {
      printf ("\n\n%s%d/%d Tests successfully completed%s\n", bash_green,
              get_num_tests (), get_num_tests (), bash_default);
    }
  else
    {
      printf ("\n\n%d/%d Tests successfully completed\n", get_num_tests (),
              get_num_tests ());
    }
  if (bash)
    {
      if (get_outputs_failed () == 0)
        {
          printf ("%s", bash_green);
        }
      else
        {
          printf ("%s", bash_red);
        }
      printf ("%d/%d Outputs successfully compared%s\n",
              get_outputs_compared () - get_outputs_failed (),
              get_outputs_compared (), bash_default);
    }
  else
    {
      printf ("%d/%d Outputs successfully compared\n",
              get_outputs_compared () - get_outputs_failed (),
              get_outputs_compared ());
    }
}

int
main (int argc, char **argv)
{
  int bash = 1;
  if (argc != 2 && argc != 1)
    {
      printf ("%s\n", msg_usage);
      return 1;
    }
  if (argc == 2)
    {
      if (strcmp (argv[1], option_no_bash) == 0)
        {
          bash = 0;
	} else {
          printf ("%s\n", msg_usage);
          return 1;
        }
    }
  run_all_tests (bash);
  return 0;
}
