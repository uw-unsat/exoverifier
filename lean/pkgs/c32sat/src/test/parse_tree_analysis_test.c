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
#include <stdlib.h>
#include <string.h>
#include "parse_tree_analysis_test.h"
#include "test_logging.h"
#include "../parse_tree_analysis.h"
#include "../memory_management.h"
#include "../error_management.h"
#include "../scanner.h"
#include "../parser.h"
#include "../hash_table.h"
#include "../parse_tree.h"
#include "../linked_list.h"
#include "../config.h"

void
test_analyse_parse_tree_boolean_variables_only (char *file,
                                                int var_size_expected,
                                                int first_free_id_expected)
{
  FILE *finput = fopen (file, "r");
  ParseTree *tree = NULL;
  LinkedList *variables = NULL;
  LinkedListIterator *iterator = NULL;
  VariableContext *context = NULL;
  HashTable *table = NULL;
  Scanner *scanner;
  Parser *parser = NULL;
  char *variable = NULL;
  int first_free_id = 0;
  init_error_management (stderr);
  init_memory_management ();
  scanner = create_scanner (finput);
  parser = create_parser (scanner);
  tree = parse (parser);
  table = analyse_parse_tree (tree, &variables, &first_free_id);
  assert (first_free_id == first_free_id_expected);
  delete_parse_tree (tree);
  assert (variables->size == var_size_expected);
  iterator = create_linked_list_iterator (variables);
  while (has_next_linked_list_iterator (iterator))
    {
      variable = (char *) next_linked_list_iterator (iterator);
      context =
        (VariableContext *) lookup_hash_table (&table, (void *) variable);
      assert (context->bool == b_true);
      free_c32sat (variable, sizeof (char) * (strlen (variable) + 1));
    }
  delete_linked_list_iterator (iterator);
  delete_linked_list (variables);
  delete_hash_table (table, b_true);
  delete_parser (parser);
  delete_scanner (scanner);
  finalise_memory_management ();
  fclose (finput);
}

void
test_analyse_parse_tree_integer_constant ()
{
  test_analyse_parse_tree_boolean_variables_only ("input/basic2.c32sat", 0,
                                                  1);
}

void
test_analyse_parse_tree_bool_simple_variable ()
{
  test_analyse_parse_tree_boolean_variables_only ("input/basic1.c32sat", 1,
                                                  2);
}

void
test_analyse_parse_tree_dimp ()
{
  test_analyse_parse_tree_boolean_variables_only
    ("input/parse_tree_analysis_dimp.c32sat", 2, 3);
}

void
test_analyse_parse_tree_imp ()
{
  test_analyse_parse_tree_boolean_variables_only
    ("input/parse_tree_analysis_imp.c32sat", 2, 3);
}

void
test_analyse_parse_tree_or ()
{
  test_analyse_parse_tree_boolean_variables_only
    ("input/parse_tree_analysis_or.c32sat", 2, 3);
}

void
test_analyse_parse_tree_and ()
{
  test_analyse_parse_tree_boolean_variables_only
    ("input/parse_tree_analysis_and.c32sat", 2, 3);
}

void
test_analyse_parse_tree_not ()
{
  test_analyse_parse_tree_boolean_variables_only
    ("input/parse_tree_analysis_not.c32sat", 1, 2);
}

void
test_analyse_parse_tree_32bit_variables_only (char *file,
                                              int var_size_expected,
                                              int first_free_id_expected)
{
  FILE *finput = fopen (file, "r");
  ParseTree *tree = NULL;
  LinkedList *variables = NULL;
  LinkedListIterator *iterator = NULL;
  VariableContext *context = NULL;
  HashTable *table = NULL;
  Scanner *scanner;
  Parser *parser = NULL;
  char *variable = NULL;
  int first_free_id = 0;
  init_error_management (stderr);
  init_memory_management ();
  scanner = create_scanner (finput);
  parser = create_parser (scanner);
  tree = parse (parser);
  table = analyse_parse_tree (tree, &variables, &first_free_id);
  assert (first_free_id == first_free_id_expected);
  delete_parse_tree (tree);
  assert (variables->size == var_size_expected);
  iterator = create_linked_list_iterator (variables);
  while (has_next_linked_list_iterator (iterator))
    {
      variable = (char *) next_linked_list_iterator (iterator);
      context =
        (VariableContext *) lookup_hash_table (&table, (void *) variable);
      assert (context->bool == b_false);
      free_c32sat (variable, sizeof (char) * (strlen (variable) + 1));
    }
  delete_linked_list_iterator (iterator);
  delete_linked_list (variables);
  delete_hash_table (table, b_true);
  delete_parser (parser);
  delete_scanner (scanner);
  finalise_memory_management ();
  fclose (finput);
}

void
test_analyse_parse_tree_ite ()
{
  test_analyse_parse_tree_32bit_variables_only
    ("input/parse_tree_analysis_ite.c32sat", 3, 97);
}

void
test_analyse_parse_tree_b_or ()
{
  test_analyse_parse_tree_32bit_variables_only
    ("input/parse_tree_analysis_b_or.c32sat", 2, 65);
}

void
test_analyse_parse_tree_b_xor ()
{
  test_analyse_parse_tree_32bit_variables_only
    ("input/parse_tree_analysis_b_xor.c32sat", 2, 65);
}

void
test_analyse_parse_tree_b_and ()
{
  test_analyse_parse_tree_32bit_variables_only
    ("input/parse_tree_analysis_b_and.c32sat", 2, 65);
}

void
test_analyse_parse_tree_eq ()
{
  test_analyse_parse_tree_32bit_variables_only
    ("input/parse_tree_analysis_eq.c32sat", 2, 65);
}

void
test_analyse_parse_tree_neq ()
{
  test_analyse_parse_tree_32bit_variables_only
    ("input/parse_tree_analysis_neq.c32sat", 2, 65);
}

void
test_analyse_parse_tree_lt ()
{
  test_analyse_parse_tree_32bit_variables_only
    ("input/parse_tree_analysis_lt.c32sat", 2, 65);
}

void
test_analyse_parse_tree_lte ()
{
  test_analyse_parse_tree_32bit_variables_only
    ("input/parse_tree_analysis_lte.c32sat", 2, 65);
}

void
test_analyse_parse_tree_gt ()
{
  test_analyse_parse_tree_32bit_variables_only
    ("input/parse_tree_analysis_gt.c32sat", 2, 65);
}

void
test_analyse_parse_tree_gte ()
{
  test_analyse_parse_tree_32bit_variables_only
    ("input/parse_tree_analysis_gte.c32sat", 2, 65);
}

void
test_analyse_parse_tree_shiftl ()
{
  test_analyse_parse_tree_32bit_variables_only
    ("input/parse_tree_analysis_shiftl.c32sat", 2, 65);
}

void
test_analyse_parse_tree_shiftr ()
{
  test_analyse_parse_tree_32bit_variables_only
    ("input/parse_tree_analysis_shiftr.c32sat", 2, 65);
}

void
test_analyse_parse_tree_plus ()
{
  test_analyse_parse_tree_32bit_variables_only
    ("input/parse_tree_analysis_plus.c32sat", 2, 65);
}

void
test_analyse_parse_tree_binary_minus ()
{
  test_analyse_parse_tree_32bit_variables_only
    ("input/parse_tree_analysis_binary_minus.c32sat", 2, 65);
}

void
test_analyse_parse_tree_mult ()
{
  test_analyse_parse_tree_32bit_variables_only
    ("input/parse_tree_analysis_mult.c32sat", 2, 65);
}

void
test_analyse_parse_tree_div ()
{
  test_analyse_parse_tree_32bit_variables_only
    ("input/parse_tree_analysis_div.c32sat", 2, 65);
}

void
test_analyse_parse_tree_mod ()
{
  test_analyse_parse_tree_32bit_variables_only
    ("input/parse_tree_analysis_mod.c32sat", 2, 65);
}

void
test_analyse_parse_tree_unary_minus ()
{
  test_analyse_parse_tree_32bit_variables_only
    ("input/parse_tree_analysis_unary_minus.c32sat", 1, 33);
}

void
test_analyse_parse_tree_comp ()
{
  test_analyse_parse_tree_32bit_variables_only
    ("input/parse_tree_analysis_comp.c32sat", 1, 33);
}

void
test_analyse_parse_tree_mixed_1 ()
{
  test_analyse_parse_tree_32bit_variables_only
    ("input/parse_tree_analysis_mixed_1.c32sat", 2, 65);
}

void
test_analyse_parse_tree_mixed_2 ()
{
  test_analyse_parse_tree_32bit_variables_only
    ("input/parse_tree_analysis_mixed_2.c32sat", 2, 65);
}

void
test_analyse_parse_tree_mixed_3 ()
{
  test_analyse_parse_tree_32bit_variables_only
    ("input/parse_tree_analysis_mixed_3.c32sat", 3, 97);
}

void
test_analyse_parse_tree_mixed_4 ()
{
  test_analyse_parse_tree_32bit_variables_only
    ("input/parse_tree_analysis_mixed_4.c32sat", 2, 65);
}

void
test_analyse_parse_tree_mixed_5 ()
{
  test_analyse_parse_tree_32bit_variables_only
    ("input/parse_tree_analysis_mixed_5.c32sat", 2, 65);
}

void
test_analyse_parse_tree_too_many_variables_error ()
{
  FILE *finput = fopen ("input/bool_1025_var.c32sat", "r");
  FILE *err_output =
    fopen ("output/parse_tree_analysis_too_many_variables_error_output.txt",
           "w");
  ParseTree *tree = NULL;
  LinkedList *variables = NULL;
  LinkedListIterator *iterator = NULL;
  HashTable *table = NULL;
  Scanner *scanner;
  Parser *parser = NULL;
  char *variable = NULL;
  const int supported_vars = 3;
  int first_free_id = 0;
  init_error_management (err_output);
  init_memory_management ();
  assert (!ext_too_many_variables_error_occured);
  ext_number_of_supported_variables = supported_vars;
  scanner = create_scanner (finput);
  parser = create_parser (scanner);
  tree = parse (parser);
  table = analyse_parse_tree (tree, &variables, &first_free_id);
  assert (ext_too_many_variables_error_occured);
  delete_parse_tree (tree);
  assert (variables->size == supported_vars);
  iterator = create_linked_list_iterator (variables);
  while (has_next_linked_list_iterator (iterator))
    {
      variable = (char *) next_linked_list_iterator (iterator);
      free_c32sat (variable, sizeof (char) * (strlen (variable) + 1));
    }
  delete_linked_list_iterator (iterator);
  delete_linked_list (variables);
  delete_hash_table (table, b_true);
  delete_parser (parser);
  delete_scanner (scanner);
  finalise_memory_management ();
  fclose (finput);
  fclose (err_output);
  ext_number_of_supported_variables =
    CONFIG_DEFAULT_NUMBER_OF_SUPPORTED_VARIABLES;
}

void
test_analyse_parse_tree_too_many_aigs_error_bool ()
{
  FILE *finput = fopen ("input/bool_1025_var.c32sat", "r");
  FILE *err_output =
    fopen ("output/parse_tree_analysis_too_many_aigs_error_bool_output.txt",
           "w");
  ParseTree *tree = NULL;
  LinkedList *variables = NULL;
  LinkedListIterator *iterator = NULL;
  HashTable *table = NULL;
  Scanner *scanner;
  Parser *parser = NULL;
  char *variable = NULL;
  int first_free_id = 0;
  init_error_management (err_output);
  init_memory_management ();
  assert (!ext_too_many_aigs_error_occured);
  ext_number_of_supported_aigs = 1024;
  scanner = create_scanner (finput);
  parser = create_parser (scanner);
  tree = parse (parser);
  table = analyse_parse_tree (tree, &variables, &first_free_id);
  assert (ext_too_many_aigs_error_occured);
  delete_parse_tree (tree);
  assert (variables->size == 1025);
  iterator = create_linked_list_iterator (variables);
  while (has_next_linked_list_iterator (iterator))
    {
      variable = (char *) next_linked_list_iterator (iterator);
      free_c32sat (variable, sizeof (char) * (strlen (variable) + 1));
    }
  delete_linked_list_iterator (iterator);
  delete_linked_list (variables);
  delete_hash_table (table, b_true);
  delete_parser (parser);
  delete_scanner (scanner);
  finalise_memory_management ();
  fclose (finput);
  fclose (err_output);
  ext_number_of_supported_aigs = CONFIG_DEFAULT_NUMBER_OF_SUPPORTED_AIGS;
}

void
test_analyse_parse_tree_too_many_aigs_error_32bit ()
{
  FILE *finput = fopen ("sat/sat4.c32sat", "r");
  FILE *err_output =
    fopen ("output/parse_tree_analysis_too_many_aigs_error_32bit_output.txt",
           "w");
  ParseTree *tree = NULL;
  LinkedList *variables = NULL;
  LinkedListIterator *iterator = NULL;
  HashTable *table = NULL;
  Scanner *scanner;
  Parser *parser = NULL;
  char *variable = NULL;
  int first_free_id = 0;
  init_error_management (err_output);
  init_memory_management ();
  assert (!ext_too_many_aigs_error_occured);
  ext_number_of_supported_aigs = 63;
  scanner = create_scanner (finput);
  parser = create_parser (scanner);
  tree = parse (parser);
  table = analyse_parse_tree (tree, &variables, &first_free_id);
  assert (ext_too_many_aigs_error_occured);
  delete_parse_tree (tree);
  assert (variables->size == 2);
  iterator = create_linked_list_iterator (variables);
  while (has_next_linked_list_iterator (iterator))
    {
      variable = (char *) next_linked_list_iterator (iterator);
      free_c32sat (variable, sizeof (char) * (strlen (variable) + 1));
    }
  delete_linked_list_iterator (iterator);
  delete_linked_list (variables);
  delete_hash_table (table, b_true);
  delete_parser (parser);
  delete_scanner (scanner);
  finalise_memory_management ();
  fclose (finput);
  fclose (err_output);
  ext_number_of_supported_aigs = CONFIG_DEFAULT_NUMBER_OF_SUPPORTED_AIGS;
}

void
run_parse_tree_analysis_tests ()
{
  run_test (test_analyse_parse_tree_integer_constant);
  run_test (test_analyse_parse_tree_bool_simple_variable);
  run_test (test_analyse_parse_tree_dimp);
  run_test (test_analyse_parse_tree_imp);
  run_test (test_analyse_parse_tree_or);
  run_test (test_analyse_parse_tree_and);
  run_test (test_analyse_parse_tree_not);
  run_test (test_analyse_parse_tree_ite);
  run_test (test_analyse_parse_tree_b_or);
  run_test (test_analyse_parse_tree_b_xor);
  run_test (test_analyse_parse_tree_b_and);
  run_test (test_analyse_parse_tree_eq);
  run_test (test_analyse_parse_tree_neq);
  run_test (test_analyse_parse_tree_lt);
  run_test (test_analyse_parse_tree_lte);
  run_test (test_analyse_parse_tree_gt);
  run_test (test_analyse_parse_tree_gte);
  run_test (test_analyse_parse_tree_shiftl);
  run_test (test_analyse_parse_tree_shiftr);
  run_test (test_analyse_parse_tree_plus);
  run_test (test_analyse_parse_tree_binary_minus);
  run_test (test_analyse_parse_tree_mult);
  run_test (test_analyse_parse_tree_div);
  run_test (test_analyse_parse_tree_mod);
  run_test (test_analyse_parse_tree_unary_minus);
  run_test (test_analyse_parse_tree_comp);
  run_test (test_analyse_parse_tree_mixed_1);
  run_test (test_analyse_parse_tree_mixed_2);
  run_test (test_analyse_parse_tree_mixed_3);
  run_test (test_analyse_parse_tree_mixed_4);
  run_test (test_analyse_parse_tree_mixed_5);
  run_test (test_analyse_parse_tree_too_many_variables_error);
  check_output
    ("output/parse_tree_analysis_too_many_variables_error_expected.txt",
     "output/parse_tree_analysis_too_many_variables_error_output.txt");
  run_test (test_analyse_parse_tree_too_many_aigs_error_bool);
  check_output
    ("output/parse_tree_analysis_too_many_aigs_error_bool_expected.txt",
     "output/parse_tree_analysis_too_many_aigs_error_bool_output.txt");
  run_test (test_analyse_parse_tree_too_many_aigs_error_32bit);
  check_output
    ("output/parse_tree_analysis_too_many_aigs_error_32bit_expected.txt",
     "output/parse_tree_analysis_too_many_aigs_error_32bit_output.txt");

}
