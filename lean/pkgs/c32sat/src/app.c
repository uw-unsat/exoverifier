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
#include <string.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdarg.h>
#include "exit_codes.h"
#include "app.h"
#include "bool.h"
#include "config.h"
#include "c32sat_math.h"
#include "sat_solver.h"
#include "cnf.h"
#include "memory_management.h"
#include "error_management.h"
#include "scanner.h"
#include "parser.h"
#include "parse_tree.h"
#include "parse_tree_analysis.h"
#include "aig.h"
#include "aig_vector.h"
#include "aig_id_generation.h"
#include "aig_transformation.h"
#include "hash_table.h"
#include "parse_tree_transformation.h"
#include "linked_list.h"

#define APP_INITIAL_AIG_UNIQUE_TABLE_POWER 10

enum AppState
{
  as_start,
  as_end
};

typedef enum AppState AppState;

enum OutputMode
{
  om_binary,
  om_decimal,
  om_hex
};

typedef enum OutputMode OutputMode;

static const char *credits =
  "\n"
  "**************************\n"
  "*      C32SAT 1.4.1      *\n"
  "**************************\n"
  "* by Robert D. Brummayer *\n"
  "*          FMV           *\n"
  "*    JKU Linz Austria    *\n"
  "**************************\n"
  "*      Contributors:     *\n"
  "**************************\n"
  "*       Armin Biere      *\n" 
  "**************************\n";
static const char *usage = "Usage: c32sat [<option> ...] [input-file]";

static const char *option_pretty_print = "-p";
static const char *option_help_short = "-h";
static const char *option_help_long = "--help";
static const char *option_sat_mode = "-s";
static const char *option_tautology_mode = "-t";
static const char *option_always_defined_mode = "-ad";
static const char *option_always_undefined_mode = "-au";
static const char *option_under_approx_width = "-ua-width";
static const char *option_under_approx = "-ua";
static const char *option_no_under_approx = "-no-ua";
static const char *option_two_level_opt = "-two-level-opt";
static const char *option_no_two_level_opt = "-no-two-level-opt";
static const char *option_verbose = "-v";
static const char *option_dump_aig = "-dump-aig";
static const char *option_dump_cnf = "-dump-cnf";
static const char *option_4_bits = "-4bits";
static const char *option_8_bits = "-8bits";
static const char *option_16_bits = "-16bits";
static const char *option_32_bits = "-32bits";
static const char *option_64_bits = "-64bits";
static const char *option_binary = "-bin";
static const char *option_decimal = "-dec";
static const char *option_hex = "-hex";
static const char *option_overflow = "-overflow";
static const char *option_no_overflow = "-no-overflow";

static const char *msg_help =
  "\n"
  "where <option> is one of the following options:\n"
  "\n"
  "-s                  satisfiability mode (default)\n"
  "-t                  tautology mode\n"
  "-ad                 defined result mode\n"
  "-au                 undefined result mode\n"
  "\n"
  "-ua                 use under-approximations in SAT mode (default)\n"
  "-ua-width <width>   use <width> as starting under aproximation width (default 1)\n"
  "-no-ua              do not use under-approximations in SAT mode\n"
  "\n"
  "-two-level-opt      use two level AIG optimization rules (default)\n"
  "-no-two-level-opt   do not use two level AIG optimization rules\n"
  "\n"
  "-overflow           allow two's complement integer overflow\n"
  "-no-overflow        treat overflow as undefined (default)\n"
  "\n"
  "-4bits              use  4 bit integers\n"
  "-8bits              use  8 bit integers\n"
  "-16bits             use 16 bit integers\n"
  "-32bits             use 32 bit integers (default)\n"
  "-64bits             use 64 bit integers\n"
  "\n"
  "-bin                print binary output\n"
  "-dec                print decimal output (default)\n"
  "-hex                print hexadecimal output\n"
  "\n"
  "-h, --help          print this command line option summary\n"
  "-v                  use verbose output \n"
  "-p                  parse and print the input only\n"
  "-dump-aig           dump the generated AIG\n"
  "-dump-cnf           dump the generated CNF";

static const char *msg_tautology = "FORMULA IS TAUTOLOGICAL";
static const char *msg_no_tautology = "FORMULA IS NOT TAUTOLOGICAL";
static const char *msg_satisfiable = "FORMULA IS SATISFIABLE";
static const char *msg_unsatisfiable = "FORMULA IS UNSATISFIABLE";
static const char *msg_always_defined =
  "THE RESULT OF THE FORMULA IS ALWAYS DEFINED (C99)";
static const char *msg_not_always_defined =
  "THE RESULT OF THE FORMULA IS NOT ALWAYS DEFINED (C99)";
static const char *msg_always_undefined =
  "THE RESULT OF THE FORMULA IS ALWAYS UNDEFINED (C99)";
static const char *msg_not_always_undefined =
  "THE RESULT OF THE FORMULA IS NOT ALWAYS UNDEFINED (C99)";
static const char *msg_counter_example = "COUNTER-EXAMPLE:";
static const char *msg_assignments = "ASSIGNMENT:";

static FILE *g_output;
static SatSolver *g_sat_solver;
static HashTable *g_symbol_table;
static OutputMode g_output_mode;

static void
print_assignment (char *variable)
{
  int i = 0;
  int temp = 0;
  VariableContext *context = NULL;
  int result_bin[ext_number_of_bits];
  char *result_string = NULL;
  assert (variable != NULL);
  context = (VariableContext *) lookup_hash_table (&g_symbol_table, variable);
  if (context->bool)
    {
      result_bin[0] =
        g_sat_solver->ptr_sat_solver_deref (g_sat_solver->solver,
                                            context->start_id);
      for (i = 1; i < ext_number_of_bits; i++)
        {
          result_bin[i] = 0;
        }
    }
  else
    {
      if (ext_app_mode == am_sat_ua)
        {
          for (i = 0; i < ext_approx_number_of_bits; i++)
            {
              result_bin[i] =
                g_sat_solver->ptr_sat_solver_deref (g_sat_solver->solver,
                                                    i + context->start_id);
            }
          if (ext_approx_number_of_bits < ext_number_of_bits)
            {
              temp =
                g_sat_solver->
                ptr_sat_solver_deref (g_sat_solver->solver,
                                      ext_approx_number_of_bits +
                                      context->start_id);
              for (i = ext_approx_number_of_bits; i < ext_number_of_bits; i++)
                {
                  result_bin[i] = temp;
                }
            }
        }
      else
        {
          for (i = 0; i < ext_number_of_bits; i++)
            {
              result_bin[i] =
                g_sat_solver->ptr_sat_solver_deref (g_sat_solver->solver,
                                                    i + context->start_id);
            }
        }
    }
  fprintf (g_output, "%s = ", variable);
  if (g_output_mode == om_binary)
    {
      for (i = ext_number_of_bits - 1; i >= 0; i--)
        {
          fprintf (g_output, "%d", result_bin[i]);
        }
    }
  else if (g_output_mode == om_decimal)
    {
      fprintf (g_output, "%lld",
               bin_2_long_long_c32sat_math (result_bin, ext_number_of_bits));
    }
  else
    {
      assert (g_output_mode == om_hex);
      result_string = bin_2_hex_c32sat_math (result_bin, ext_number_of_bits);
      fprintf (g_output, "%s", result_string);
      free_c32sat (result_string,
                   sizeof (char) * (strlen (result_string) + 1));
    }
  fprintf (g_output, "\n");
}

static int
compare_names (const void *name1, const void *name2)
{
  return strcmp (*(char **) name1, *(char **) name2);
}

static void
print_assignments (LinkedList * variables)
{
  int i = 0;
  int size = 0;
  char **names = NULL;
  LinkedListIterator *iterator = NULL;
  assert (variables != NULL);
  iterator = create_linked_list_iterator (variables);
  size = variables->size;
  names = (char **) malloc_c32sat (sizeof (char *) * size);
  while (has_next_linked_list_iterator (iterator))
    {
      names[i] = (char *) next_linked_list_iterator (iterator);
      i++;
    }
  qsort (names, (size_t)size, sizeof (char *), compare_names);
  for (i = 0; i < size; i++)
    {
      print_assignment (names[i]);
    }
  free_c32sat (names, sizeof (char *) * size);
  delete_linked_list_iterator (iterator);
}

static void
print_constant_assignments (LinkedList * variables)
{
  LinkedListIterator *iterator = NULL;
  assert (variables != NULL);
  iterator = create_linked_list_iterator (variables);
  while (has_next_linked_list_iterator (iterator))
    {
      fprintf (g_output, "%s = 0\n",
               (char *) next_linked_list_iterator (iterator));
    }
  delete_linked_list_iterator (iterator);
}

static int
invalid_usage ()
{
  error (e_app_invalid_usage, 0, 0, 0, usage);
  return ec_invalid_usage;
}

static void
print_message (const char *message)
{
  fprintf (g_output, "%s\n", message);
}

static void
print_message_va_arg (const char *message, ...)
{
  va_list list;
  va_start (list, message);
  vfprintf (g_output, message, list);
  va_end (list);
  fprintf (g_output, "\n");
}

static void
feed_sat_solver (CNF * cnf)
{
  CNFIterator *cnf_iterator = create_cnf_iterator (cnf);
  while (has_next_cnf_iterator (cnf_iterator))
    {
      g_sat_solver->ptr_sat_solver_add (g_sat_solver->solver,
                                        next_cnf_iterator (cnf_iterator));
    }
  delete_cnf_iterator (cnf_iterator);
}

static void
delete_variables (LinkedList * variables)
{
  char *cur_var = NULL;
  LinkedListIterator *iterator = create_linked_list_iterator (variables);
  while (has_next_linked_list_iterator (iterator))
    {
      cur_var = next_linked_list_iterator (iterator);
      free_c32sat (cur_var, sizeof (char) * (strlen (cur_var) + 1));
    }
  delete_linked_list_iterator (iterator);
  delete_linked_list (variables);
}

int
c32sat_main (int argc, char **argv, FILE * output, FILE * err_output)
{
  /* Declarations */
  char *input_filename = NULL;
  FILE *finput = stdin;
  ParseTree *tree = NULL;
  Scanner *scanner = NULL;
  Parser *parser = NULL;
  AIGUniqueTable *unique_table = NULL;
  AIGVector *aig_vector_result = NULL;
  AIG *aig_result = NULL;
  AIG *temp = NULL;
  CNF *cnf = NULL;
  LinkedList *variables = NULL;
  int first_free_id = 0;
  Bool help = b_false;
  Bool dump_aig = b_false;
  Bool dump_cnf = b_false;
  Bool verbose = b_false;
  Bool pretty_print = b_false;
  Bool under_approx_width_specified = b_false;
  ParseTreeNode *neg_node = NULL;
  AppState state = as_start;
  int i = 1;
  int sat_result = 0;
  int transformers_size = 0;
  AIG2CNFTransformer **transformers = NULL;
  AIG2CNFTransformer *selected_transformer = NULL;
  ExitCode exit_code = ec_pretty_print_success;
  assert (output != NULL && err_output != NULL);
  g_output = output;
  g_output_mode = om_decimal;
  ext_app_mode = am_sat_ua;
  ext_number_of_bits = 32;
  ext_approx_number_of_bits = 1;
  ext_allow_overflow = b_false;
  ext_two_level_opt = b_true;
  init_error_management (err_output);
  assert (sizeof (int) >= 4);
  assert (sizeof (long long int) >= 8);
  assert (sizeof (long int) == sizeof (void *));
  /* Analyse parameters */
  while (i < argc)
    {
      switch (state)
        {
        case as_start:
          if (argv[i][0] == '-')
            {                   /* Option */
              if (strcmp (argv[i], option_pretty_print) == 0)
                {
                  pretty_print = b_true;
                }
              else if (strcmp (argv[i], option_verbose) == 0)
                {
                  verbose = b_true;
                }
              else if ((strcmp (argv[i], option_help_short) == 0)
                       || (strcmp (argv[i], option_help_long) == 0))
                {
                  help = b_true;
                }
              else if (strcmp (argv[i], option_sat_mode) == 0)
                {
                  if (ext_app_mode != am_sat)
                    {
                      ext_app_mode = am_sat_ua;
                    }
                }
              else if (strcmp (argv[i], option_under_approx) == 0)
                {
                  if (ext_app_mode == am_sat)
                    {
                      ext_app_mode = am_sat_ua;
                    }
                }
              else if (strcmp (argv[i], option_under_approx_width) == 0)
                {
                  ext_approx_number_of_bits = atoi (argv[++i]);
                  under_approx_width_specified = b_true;
                }
              else if (strcmp (argv[i], option_no_under_approx) == 0)
                {
                  if (ext_app_mode == am_sat_ua)
                    {
                      ext_app_mode = am_sat;
                    }
                }
              else if (strcmp (argv[i], option_two_level_opt) == 0)
                {
                  ext_two_level_opt = b_true;
                }
              else if (strcmp (argv[i], option_no_two_level_opt) == 0)
                {
                  ext_two_level_opt = b_false;
                }
              else if (strcmp (argv[i], option_tautology_mode) == 0)
                {
                  ext_app_mode = am_taut;
                }
              else if (strcmp (argv[i], option_always_defined_mode) == 0)
                {
                  ext_app_mode = am_always_def;
                }
              else if (strcmp (argv[i], option_always_undefined_mode) == 0)
                {
                  ext_app_mode = am_always_undef;
                }
              else if (strcmp (argv[i], option_dump_aig) == 0)
                {
                  dump_aig = b_true;
                }
              else if (strcmp (argv[i], option_dump_cnf) == 0)
                {
                  dump_cnf = b_true;
                }
              else if (strcmp (argv[i], option_4_bits) == 0)
                {
                  ext_number_of_bits = 4;
                }
              else if (strcmp (argv[i], option_8_bits) == 0)
                {
                  ext_number_of_bits = 8;
                }
              else if (strcmp (argv[i], option_16_bits) == 0)
                {
                  ext_number_of_bits = 16;
                }
              else if (strcmp (argv[i], option_32_bits) == 0)
                {
                  ext_number_of_bits = 32;
                }
              else if (strcmp (argv[i], option_64_bits) == 0)
                {
                  ext_number_of_bits = 64;
                }
              else if (strcmp (argv[i], option_binary) == 0)
                {
                  g_output_mode = om_binary;
                }
              else if (strcmp (argv[i], option_decimal) == 0)
                {
                  g_output_mode = om_decimal;
                }
              else if (strcmp (argv[i], option_hex) == 0)
                {
                  g_output_mode = om_hex;
                }
              else if (strcmp (argv[i], option_overflow) == 0)
                {
                  ext_allow_overflow = b_true;
                }
              else if (strcmp (argv[i], option_no_overflow) == 0)
                {
                  ext_allow_overflow = b_false;
                }
              else
                {
                  error (e_app_invalid_usage_unknown_option, 0, 0, 0,
                         argv[i]);
                  return ec_invalid_usage;
                }
            }
          else
            {                   /* Input file */
              input_filename = argv[i];
              state = as_end;
            }
          break;
        case as_end:
          return invalid_usage ();
          break;
        default:
          assert (0);
          break;
        }
      i++;
    }
  if (help)
    {
      fprintf (output, "%s\n", credits);
      fprintf (output, "%s\n", usage);
      fprintf (output, "%s\n", msg_help);
      fflush (output);
      return ec_help_success;
    }
  if ((ext_approx_number_of_bits >= ext_number_of_bits)
      || ((ext_approx_number_of_bits != 1) && (ext_approx_number_of_bits != 2)
          && (ext_approx_number_of_bits != 4)
          && (ext_approx_number_of_bits != 8)
          && (ext_approx_number_of_bits != 16)
          && (ext_approx_number_of_bits != 32)))
    {
      error (e_app_invalid_under_approx_width, 0, 0, 0, NULL);
      return ec_invalid_usage;
    }
  if ((ext_app_mode == am_sat_ua) && (dump_cnf || dump_aig)
      && !under_approx_width_specified)
    {
      error (e_app_dump_no_under_approx_width, 0, 0, 0, NULL);
      return ec_invalid_usage;
    }
  if (input_filename != NULL)
    {
      finput = fopen (input_filename, "r");
      if (finput == NULL)
        {
          error (e_app_input_error, 0, 0, 0, input_filename);
          return ec_io_error;
        }
    }
  init_memory_management ();
  /* AIG2CNF transformer can be selected here */
  transformers = create_aig_2_cnf_transformers (&transformers_size);
  assert (transformers_size > 0);
  selected_transformer = transformers[0];
  scanner = create_scanner (finput);
  parser = create_parser (scanner);
  /* Parse input */
  if (verbose && !pretty_print && !dump_cnf && !dump_aig)
    {
      print_message ("Parsing input...");
    }
  tree = parse (parser);
  if (!has_error_occured ())
    {
      if (pretty_print)
        {
          pretty_print_parse_tree (tree, output);
          exit_code = ec_pretty_print_success;
        }
      else
        {
          if (ext_app_mode == am_taut)
            {
              neg_node = create_parse_tree_node (ptn_not);
              assert (neg_node != NULL);
              parse_tree_node_first_child (neg_node) = tree->root;
              tree->root = neg_node;
              assert (tree->root != NULL);
            }
          assert (!ext_too_many_variables_error_occured);
        UA_REFINEMENT:
          if (ext_app_mode == am_sat_ua)
            {
              if (ext_approx_number_of_bits < ext_number_of_bits)
                {
                  if (dump_cnf)
                    {
                      print_message_va_arg
                        ("c CNF for under-approximation width of %d",
                         ext_approx_number_of_bits);
                    }
                  else if (dump_aig)
                    {
                      print_message_va_arg
                        ("c AIG for under-approximation width of %d",
                         ext_approx_number_of_bits);
                    }
                  else
                    {
                      print_message_va_arg
                        ("Trying to solve SAT instance with an under-approximation width of %d ...",
                         ext_approx_number_of_bits);
                    }
                }
              else
                {
                  assert (ext_approx_number_of_bits == ext_number_of_bits);

                  print_message
                    ("Couldn't find a satisfiable assignment during approximation steps");
                  print_message ("Solving entire SAT instance...");
                }
            }
          g_symbol_table =
            analyse_parse_tree (tree, &variables, &first_free_id);
          if (ext_too_many_variables_error_occured
              || ext_too_many_aigs_error_occured)
            {
              delete_aig_2_cnf_transformers (transformers, transformers_size);
              delete_parse_tree (tree);
              delete_hash_table (g_symbol_table, b_true);
              delete_variables (variables);
              delete_parser (parser);
              delete_scanner (scanner);
              finalise_memory_management ();
              fflush (output);
              fflush (err_output);
              if (finput != stdin)
                {
                  fclose (finput);
                }
              if (ext_too_many_variables_error_occured)
                {
                  return ec_too_many_variables;
                }
              else
                {
                  return ec_too_many_aigs;
                }
            }
          if (verbose && !dump_cnf && !dump_aig)
            {
              print_message_va_arg ("Number of variables in formula: %d",
                                    variables->size);
            }
          unique_table =
            create_aig_unique_table (APP_INITIAL_AIG_UNIQUE_TABLE_POWER);
          assert (!ext_too_many_aigs_error_occured);
          aig_vector_result =
            parse_tree_2_aig_vector (&unique_table, tree, &g_symbol_table);
          if (ext_app_mode == am_sat || ext_app_mode == am_sat_ua)
            {
              temp =
                disjunction_aig_vector (&unique_table, aig_vector_result);
              aig_result =
                and_aig (&unique_table, temp,
                         invert_aig (aig_vector_result->undefined));
              release_aig (&unique_table, temp);
            }
          else if (ext_app_mode == am_taut)
            {
              temp =
                disjunction_aig_vector (&unique_table, aig_vector_result);
              aig_result =
                or_aig (&unique_table, temp, aig_vector_result->undefined);
              release_aig (&unique_table, temp);
            }
          else
            {
              if (ext_app_mode == am_always_def)
                {
                  aig_result =
                    copy_aig (&unique_table, aig_vector_result->undefined);
                }
              else
                {
                  assert (ext_app_mode == am_always_undef);
                  aig_result =
                    invert_aig (copy_aig
                                (&unique_table,
                                 aig_vector_result->undefined));
                }
              release_aig_vector (&unique_table, aig_vector_result);
            }
          if (ext_too_many_aigs_error_occured)
            {
              delete_aig_2_cnf_transformers (transformers, transformers_size);
              delete_parse_tree (tree);
              delete_hash_table (g_symbol_table, b_true);
              delete_variables (variables);
              delete_parser (parser);
              delete_scanner (scanner);
              release_aig (&unique_table, aig_result);
              if ((ext_app_mode != am_always_def)
                  && (ext_app_mode != am_always_undef))
                {
                  release_aig_vector (&unique_table, aig_vector_result);
                }
              delete_aig_vector (aig_vector_result);
              delete_aig_unique_table (unique_table, b_false);
              finalise_memory_management ();
              fflush (output);
              fflush (err_output);
              if (finput != stdin)
                {
                  fclose (finput);
                }
              return ec_too_many_aigs;
            }
          if (verbose && !dump_cnf && !dump_aig)
            {
              if (aig_result == AIG_TRUE)
                {
                  print_message ("AIG is TRUE");
                }
              else if (aig_result == AIG_FALSE)
                {
                  print_message ("AIG is FALSE");
                }
              else
                {
                  print_message_va_arg ("Number of variables in AIG: %d",
                                        unique_table->num_vars);
                  print_message_va_arg ("Number of AND gates in AIG: %d",
                                        unique_table->num_ands);
                }
            }
          if (dump_aig)
            {
              init_aig_id_generation (first_free_id);
              print_aig (aig_result, unique_table, output);
              exit_code = ec_dump_aig_success;

            }
          else
            {
              if (is_aig_constant (aig_result))
                {
                  if (dump_cnf)
                    {
                      if (aig_result == AIG_TRUE)
                        {
                          print_message ("p cnf 1 1");
                          print_message ("1 -1 0");
                        }
                      else
                        {
                          assert (aig_result == AIG_FALSE);
                          print_message ("p cnf 1 2");
                          print_message ("1 0");
                          print_message ("-1 0");
                        }
                      exit_code = ec_dump_cnf_success;
                    }
                  else
                    {
                      if (aig_result == AIG_TRUE)
                        {
                          if (ext_app_mode == am_sat
                              || ext_app_mode == am_sat_ua)
                            {
                              print_message (msg_satisfiable);
                              if (variables->size > 0)
                                {
                                  print_message (msg_assignments);
                                  print_constant_assignments (variables);
                                }
                              exit_code = ec_satisfiable;
                            }
                          else if (ext_app_mode == am_taut)
                            {
                              print_message (msg_no_tautology);
                              if (variables->size > 0)
                                {
                                  print_message (msg_counter_example);
                                  print_constant_assignments (variables);
                                }
                              exit_code = ec_no_tautology;
                            }
                          else if (ext_app_mode == am_always_def)
                            {
                              print_message (msg_not_always_defined);
                              if (variables->size > 0)
                                {
                                  print_message (msg_counter_example);
                                  print_constant_assignments (variables);
                                }
                              exit_code = ec_not_always_defined;
                            }
                          else
                            {
                              assert (ext_app_mode == am_always_undef);
                              print_message (msg_not_always_undefined);
                              if (variables->size > 0)
                                {
                                  print_message (msg_counter_example);
                                  print_constant_assignments (variables);
                                }
                              exit_code = ec_not_always_undefined;
                            }
                        }
                      else
                        {
                          if ((ext_app_mode == am_sat)
                              || (ext_app_mode == am_sat_ua
                                  && ext_approx_number_of_bits ==
                                  ext_number_of_bits))
                            {
                              print_message (msg_unsatisfiable);
                              exit_code = ec_unsatisfiable;
                            }
                          else if (ext_app_mode == am_taut)
                            {
                              print_message (msg_tautology);
                              exit_code = ec_tautology;
                            }
                          else if (ext_app_mode == am_always_def)
                            {
                              print_message (msg_always_defined);
                              exit_code = ec_always_defined;
                            }
                          else if (ext_app_mode == am_always_undef)
                            {
                              print_message (msg_always_undefined);
                              exit_code = ec_always_undefined;
                            }
                        }
                    }
                }
              else
                {
                  assert (!dump_aig);
                  g_sat_solver = create_sat_solver ();
                  cnf =
                    transform_aig_2_cnf (aig_result, first_free_id,
                                         selected_transformer);
                  if (cnf->too_many_cnf_clauses_error_occured)
                    {
                      delete_cnf (cnf);
                      delete_sat_solver (g_sat_solver);
                      delete_aig_2_cnf_transformers (transformers,
                                                     transformers_size);
                      delete_parse_tree (tree);
                      delete_hash_table (g_symbol_table, b_true);
                      delete_variables (variables);
                      delete_parser (parser);
                      delete_scanner (scanner);
                      release_aig (&unique_table, aig_result);
                      if ((ext_app_mode != am_always_def)
                          && (ext_app_mode != am_always_undef))
                        {
                          release_aig_vector (&unique_table,
                                              aig_vector_result);
                        }
                      delete_aig_vector (aig_vector_result);
                      delete_aig_unique_table (unique_table, b_false);
                      finalise_memory_management ();
                      fflush (output);
                      fflush (err_output);
                      if (finput != stdin)
                        {
                          fclose (finput);
                        }
                      return ec_too_many_cnf_clauses;
                    }
                  if (verbose && !dump_cnf && !dump_aig)
                    {
                      print_message_va_arg ("Number of CNF variables: %d",
                                            get_number_of_cnf_variables
                                            (cnf));
                      print_message_va_arg ("Number of CNF clauses: %d",
                                            get_number_of_cnf_clauses (cnf));
                    }
                  if (dump_cnf)
                    {
                      print_cnf (cnf, g_output);
                      exit_code = ec_dump_cnf_success;
                    }
                  else
                    {
                      assert (!dump_cnf && !dump_aig);
                      g_sat_solver->solver =
                        g_sat_solver->ptr_sat_solver_init ();
                      if (verbose)
                        print_message_va_arg ("Using SAT solver %s",
                                              g_sat_solver->name);
                      if (verbose)
                        print_message ("Feeding SAT solver...");
                      feed_sat_solver (cnf);
                      if (verbose)
                        print_message ("Calling SAT Solver...");
                      sat_result =
                        g_sat_solver->ptr_sat_solver_sat (g_sat_solver->
                                                          solver);
                      if (sat_result == g_sat_solver->sat_val)
                        {
                          if (ext_app_mode == am_sat
                              || ext_app_mode == am_sat_ua)
                            {
                              print_message (msg_satisfiable);
                              print_message (msg_assignments);
                              exit_code = ec_satisfiable;
                            }
                          else if (ext_app_mode == am_taut)
                            {
                              print_message (msg_no_tautology);
                              print_message (msg_counter_example);
                              exit_code = ec_no_tautology;
                            }
                          else if (ext_app_mode == am_always_def)
                            {
                              print_message (msg_not_always_defined);
                              print_message (msg_counter_example);
                              exit_code = ec_not_always_defined;
                            }
                          else
                            {
                              assert (ext_app_mode == am_always_undef);
                              print_message (msg_not_always_undefined);
                              print_message (msg_counter_example);
                              exit_code = ec_not_always_undefined;
                            }
                          print_assignments (variables);
                        }
                      else if (sat_result == g_sat_solver->unsat_val)
                        {
                          if ((ext_app_mode == am_sat)
                              || (ext_app_mode == am_sat_ua
                                  && ext_approx_number_of_bits ==
                                  ext_number_of_bits))
                            {
                              print_message (msg_unsatisfiable);
                              exit_code = ec_unsatisfiable;
                            }
                          else if (ext_app_mode == am_taut)
                            {
                              print_message (msg_tautology);
                              exit_code = ec_tautology;
                            }
                          else if (ext_app_mode == am_always_def)
                            {
                              print_message (msg_always_defined);
                              exit_code = ec_always_defined;
                            }
                          else if (ext_app_mode == am_always_undef)
                            {
                              print_message (msg_always_undefined);
                              exit_code = ec_always_undefined;
                            }
                        }
                      else
                        {
                          error (e_app_sat_solver_error, 0, 0, sat_result,
                                 NULL);
                          exit_code = ec_sat_solver_error;
                        }
                      g_sat_solver->ptr_sat_solver_finalise (g_sat_solver->
                                                             solver);
                    }
                  delete_cnf (cnf);
                  delete_sat_solver (g_sat_solver);
                }
            }
          release_aig (&unique_table, aig_result);
          if ((ext_app_mode != am_always_def)
              && (ext_app_mode != am_always_undef))
            {
              release_aig_vector (&unique_table, aig_vector_result);
            }
          delete_aig_vector (aig_vector_result);
          delete_hash_table (g_symbol_table, b_true);
          assert (unique_table->num_vars == 0);
          assert (unique_table->num_ands == 0);
          /* all AIGs should have been deleted from memory */
          delete_aig_unique_table (unique_table, b_false);
          delete_variables (variables);
        }
      if (ext_approx_number_of_bits < ext_number_of_bits &&
          ext_app_mode == am_sat_ua && !pretty_print && !dump_aig && !dump_cnf
          && exit_code != ec_satisfiable)
        {
          ext_approx_number_of_bits <<= 1;
          goto UA_REFINEMENT;
        }
    }
  else
    {
      exit_code = ec_build_parse_tree_error;
    }
  assert (tree != NULL && parser != NULL && scanner != NULL);
  delete_aig_2_cnf_transformers (transformers, transformers_size);
  delete_parse_tree (tree);
  delete_parser (parser);
  delete_scanner (scanner);
  if (verbose && !pretty_print && !dump_aig && !dump_cnf)
    {
      if (get_max_memory_used () < 1024)
        {
          print_message_va_arg
            ("\nMemory maximally allocated (without SAT solver): %lld bytes",
             get_max_memory_used ());
        }
      else if (get_max_memory_used () < 1048576)
        {
          print_message_va_arg
            ("\nMemory maximally allocated (without SAT solver): %.1f KB",
             (float) (get_max_memory_used () / 1024));
        }
      else
        {
          print_message_va_arg
            ("\nMemory maximally allocated (without SAT solver): %.1f MB",
             (float) (get_max_memory_used () / 1048576));
        }
    }
  finalise_memory_management ();
  fflush (output);
  fflush (err_output);
  if (finput != stdin)
    {
      fclose (finput);
    }
  return exit_code;
}
