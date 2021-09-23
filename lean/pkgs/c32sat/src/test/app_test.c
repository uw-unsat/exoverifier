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
#include <stdio.h>
#include <assert.h>
#include "app_test.h"
#include "test_logging.h"
#include "../exit_codes.h"
#include "../app.h"
#include "../config.h"
#include "../bool.h"
#include "../aig.h"
#include "../parse_tree_analysis.h"
#include "../error_management.h"

static char *app_name = "c32sat";

void
test_app_error_invalid_usage ()
{
  FILE *err_output = fopen ("output/app_error_invalid_usage_output.txt", "w");
  int argc = 3;
  char *argv[] =
    { app_name, "input/formula5.c32sat", "output/pp_formula5_output.txt" };
  assert (c32sat_main
          (argc, argv, stdout, err_output) == ec_invalid_usage);
  fclose (err_output);
}

void
test_app_error_invalid_usage_unknown_option ()
{
  FILE *err_output =
    fopen ("output/app_error_invalid_usage_unknown_option_output.txt", "w");
  int argc = 3;
  char *argv[] = { app_name, "-abc", "input/formula5.c32sat" };
  assert (c32sat_main
          (argc, argv, stdout, err_output) == ec_invalid_usage);
  fclose (err_output);
}

void
test_app_error_io_error ()
{
  FILE *err_output = fopen ("output/app_error_io_error_output.txt", "w");
  int argc = 2;
  char *argv[] = { app_name, "input/dontexist.c32sat" };
  assert (c32sat_main
          (argc, argv, stdout, err_output) == ec_io_error);
  fclose (err_output);
}

void
test_app_error_build_parse_tree_error ()
{
  FILE *err_output =
    fopen ("output/app_error_build_parse_tree_error_output.txt", "w");
  int argc = 3;
  char *argv[] = { app_name, "-p", "input/parser_error1.c32sat" };
  assert (c32sat_main
          (argc, argv, stdout, err_output) == ec_build_parse_tree_error);
  fclose (err_output);
}

void
test_app_error_too_many_variables ()
{
  FILE *err_output =
    fopen ("output/app_error_too_many_variables_output.txt", "w");
  int argc = 3;
  char *argv[] = { app_name, "-no-ua", "input/bool_1025_var.c32sat" };
  assert (ext_number_of_supported_variables ==
          CONFIG_DEFAULT_NUMBER_OF_SUPPORTED_VARIABLES);
  ext_number_of_supported_variables = 3;
  assert (c32sat_main
          (argc, argv, stdout, err_output) == ec_too_many_variables);
  assert (ext_too_many_variables_error_occured);
  fclose (err_output);
  ext_number_of_supported_variables =
    CONFIG_DEFAULT_NUMBER_OF_SUPPORTED_VARIABLES;
}

void
test_app_error_parse_tree_analysis_too_many_aigs ()
{
  FILE *err_output =
    fopen ("output/app_error_parse_tree_analysis_too_many_aigs_output.txt",
           "w");
  int argc = 4;
  char *argv[] = { app_name, "-s", "-no-ua", "sat/sat6.c32sat" };
  assert (ext_number_of_supported_aigs ==
          CONFIG_DEFAULT_NUMBER_OF_SUPPORTED_AIGS);
  ext_number_of_supported_aigs = 90;
  assert (c32sat_main
          (argc, argv, stdout, err_output) == ec_too_many_aigs);
  assert (ext_too_many_aigs_error_occured);
  fclose (err_output);
  ext_number_of_supported_aigs = CONFIG_DEFAULT_NUMBER_OF_SUPPORTED_AIGS;
}

void
test_app_error_aig_too_many_aigs ()
{
  FILE *err_output =
    fopen ("output/app_error_aig_too_many_aigs_output.txt", "w");
  int argc = 4;
  char *argv[] = { app_name, "-s", "-no-ua", "sat/sat6.c32sat" };
  assert (ext_number_of_supported_aigs ==
          CONFIG_DEFAULT_NUMBER_OF_SUPPORTED_AIGS);
  ext_number_of_supported_aigs = 96;
  assert (c32sat_main
          (argc, argv, stdout, err_output) == ec_too_many_aigs);
  assert (ext_too_many_aigs_error_occured);
  fclose (err_output);
  ext_number_of_supported_aigs = CONFIG_DEFAULT_NUMBER_OF_SUPPORTED_AIGS;
}

void
test_app_error_too_many_cnf_clauses ()
{
  FILE *err_output =
    fopen ("output/app_error_too_many_cnf_clauses_output.txt", "w");
  int argc = 4;
  char *argv[] = { app_name, "-s", "-no-ua", "sat/sat11.c32sat" };
  assert (ext_number_of_supported_cnf_clauses ==
          CONFIG_DEFAULT_NUMBER_OF_SUPPORTED_CNF_CLAUSES);
  ext_number_of_supported_cnf_clauses = 2;
  assert (c32sat_main
          (argc, argv, stdout, err_output) == ec_too_many_cnf_clauses);
  fclose (err_output);
  ext_number_of_supported_cnf_clauses =
    CONFIG_DEFAULT_NUMBER_OF_SUPPORTED_CNF_CLAUSES;
}

void test_app_error_invalid_under_approx_width1 (){
  FILE *err_output = fopen ("output/app_error_invalid_under_approx_width1_output.txt", "w");
  int argc = 3;
  char *argv[] =
    { app_name, "-ua-width", "6"};
  assert (c32sat_main
          (argc, argv, stdout, err_output) == ec_invalid_usage);
  fclose (err_output);
}

void test_app_error_invalid_under_approx_width2 (){
  FILE *err_output = fopen ("output/app_error_invalid_under_approx_width2_output.txt", "w");
  int argc = 3;
  char *argv[] =
    { app_name, "-ua-width", "-4"};
  assert (c32sat_main
          (argc, argv, stdout, err_output) == ec_invalid_usage);
  fclose (err_output);
}

void test_app_error_invalid_under_approx_width3 (){
  FILE *err_output = fopen ("output/app_error_invalid_under_approx_width3_output.txt", "w");
  int argc = 4;
  char *argv[] =
    { app_name, "-ua-width", "4", "-4bits"};
  assert (c32sat_main
          (argc, argv, stdout, err_output) == ec_invalid_usage);
  fclose (err_output);
}

void test_app_error_dump_no_under_approx_width1 (){
  FILE *err_output = fopen ("output/app_error_dump_no_under_approx_width1_output.txt", "w");
  int argc =2;
  char *argv[] =
    { app_name, "-dump-cnf"};
  assert (c32sat_main
          (argc, argv, stdout, err_output) == ec_invalid_usage);
  fclose (err_output);
}

void test_app_error_dump_no_under_approx_width2 (){
  FILE *err_output = fopen ("output/app_error_dump_no_under_approx_width2_output.txt", "w");
  int argc =2;
  char *argv[] =
    { app_name, "-dump-aig"};
  assert (c32sat_main
          (argc, argv, stdout, err_output) == ec_invalid_usage);
  fclose (err_output);
}

void
test_app_pretty_print_formula1 ()
{
  int argc = 3;
  FILE *output = fopen ("output/pp_formula1_output.txt", "w");
  char *argv[] = { app_name, "-p", "input/formula1.c32sat" };
  assert (c32sat_main
          (argc, argv, output, stderr) == ec_pretty_print_success);
  fclose (output);
}

void
test_app_pretty_print_formula2 ()
{
  int argc = 3;
  FILE *output = fopen ("output/pp_formula2_output.txt", "w");
  char *argv[] = { app_name, "-p", "input/formula2.c32sat" };
  assert (c32sat_main
          (argc, argv, output, stderr) == ec_pretty_print_success);
  fclose (output);
}

void
test_app_pretty_print_formula3 ()
{
  int argc = 3;
  FILE *output = fopen ("output/pp_formula3_output.txt", "w");
  char *argv[] = { app_name, "-p", "input/formula3.c32sat" };
  assert (c32sat_main
          (argc, argv, output, stderr) == ec_pretty_print_success);
  fclose (output);
}

void
test_app_pretty_print_formula4 ()
{
  int argc = 3;
  FILE *output = fopen ("output/pp_formula4_output.txt", "w");
  char *argv[] = { app_name, "-p", "input/formula4.c32sat" };
  assert (c32sat_main
          (argc, argv, output, stderr) == ec_pretty_print_success);
  fclose (output);
}

void
test_app_pretty_print_ignore_other_options ()
{
  int argc = 4;
  FILE *output = fopen ("output/pp_formula1_output.txt", "w");
  char *argv[] = { app_name, "-s", "-p",
    "input/formula1.c32sat"
  };
  assert (c32sat_main
          (argc, argv, output, stderr) == ec_pretty_print_success);
  fclose (output);
}

void
test_app_help ()
{
  FILE *output = tmpfile ();
  int argc = 2;
  char *argv[] = { app_name, "-h" };
  assert (c32sat_main
          (argc, argv, output, stderr) == ec_help_success);
  fclose (output);
}

void
test_app_help_ignore_other_options ()
{
  FILE *output = tmpfile ();
  int argc = 6;
  char *argv[] = { app_name, "-p", "-s", "-8bits", "-h",
    "input/formula1.c32sat"
  };
  assert (c32sat_main
          (argc, argv, output, stderr) == ec_help_success);
  fclose (output);
}

void
test_app_return_dump_aig (char *file_name)
{
  FILE *output = tmpfile ();
  int argc = 4;
  char *argv[] = { app_name, "-dump-aig", "-no-ua", file_name };
  assert (c32sat_main
          (argc, argv, output, stderr) == ec_dump_aig_success);
  fclose (output);
}

void
test_app_return_dump_aig_1 ()
{
  test_app_return_dump_aig ("input/formula1.c32sat");
}

void
test_app_return_dump_aig_2 ()
{
  test_app_return_dump_aig ("input/formula2.c32sat");
}

void
test_app_return_dump_aig_3 ()
{
  test_app_return_dump_aig ("input/formula3.c32sat");
}

void
test_app_return_dump_cnf (char *file_name)
{
  FILE *output = tmpfile ();
  int argc = 4;
  char *argv[] = { app_name, "-dump-cnf", "-no-ua", file_name };
  assert (c32sat_main
          (argc, argv, output, stderr) == ec_dump_cnf_success);
  fclose (output);
}

void
test_app_return_dump_cnf_1 ()
{
  test_app_return_dump_cnf ("input/formula1.c32sat");
}

void
test_app_return_dump_cnf_2 ()
{
  test_app_return_dump_cnf ("input/formula2.c32sat");
}

void
test_app_return_dump_cnf_3 ()
{
  test_app_return_dump_cnf ("input/formula3.c32sat");
}

void
test_app_sat (char *file_name)
{
  FILE *output = tmpfile ();
  int argc = 5;
  char *argv[] =
    { app_name, "-s", "-no-ua", "-no-overflow", file_name };
  assert (c32sat_main
          (argc, argv, output, stderr) == ec_satisfiable);
  fclose (output);
}

void
test_app_sat_1 ()
{
  test_app_sat ("sat/sat1.c32sat");
}

void
test_app_sat_2 ()
{
  test_app_sat ("sat/sat2.c32sat");
}

void
test_app_sat_3 ()
{
  test_app_sat ("sat/sat3.c32sat");
}

void
test_app_sat_4 ()
{
  test_app_sat ("sat/sat4.c32sat");
}

void
test_app_sat_5 ()
{
  test_app_sat ("sat/sat5.c32sat");
}

void
test_app_sat_6 ()
{
  test_app_sat ("sat/sat6.c32sat");
}

void
test_app_sat_7 ()
{
  test_app_sat ("sat/sat7.c32sat");
}

void
test_app_sat_8 ()
{
  test_app_sat ("sat/sat8.c32sat");
}

void
test_app_sat_9 ()
{
  test_app_sat ("sat/sat9.c32sat");
}

void
test_app_sat_10 ()
{
  test_app_sat ("sat/sat10.c32sat");
}

void
test_app_sat_11 ()
{
  test_app_sat ("sat/sat11.c32sat");
}

void
test_app_sat_12 ()
{
  test_app_sat ("sat/sat12.c32sat");
}

void
test_app_sat_13 ()
{
  test_app_sat ("sat/sat13.c32sat");
}

void
test_app_sat_14 ()
{
  test_app_sat ("sat/sat14.c32sat");
}

void
test_app_sat_15 ()
{
  test_app_sat ("sat/sat15.c32sat");
}

void
test_app_sat_16 ()
{
  test_app_sat ("sat/sat16.c32sat");
}

void
test_app_sat_17 ()
{
  test_app_sat ("sat/sat17.c32sat");
}

void
test_app_sat_18 ()
{
  test_app_sat ("sat/sat18.c32sat");
}

void
test_app_sat_19 ()
{
  test_app_sat ("sat/sat19.c32sat");
}

void
test_app_satua (char *file_name, int sat)
{
  FILE *output = tmpfile ();
  int argc = 5;
  int expected = sat ? ec_satisfiable : ec_unsatisfiable;
  char *argv[] = { app_name, "-s", "-ua", "-no-overflow", file_name };
  assert (c32sat_main
          (argc, argv, output, stderr) == expected);
  fclose (output);
}

void
test_app_satua_1 ()
{
  test_app_satua ("satua/satua1.c32sat", 1);
  assert (ext_approx_number_of_bits == 1);
}

void
test_app_satua_2 ()
{
  test_app_satua ("satua/satua2.c32sat", 1);
  assert (ext_approx_number_of_bits == 1);
}

void
test_app_satua_3 ()
{
  test_app_satua ("satua/satua3.c32sat", 1);
  assert (ext_approx_number_of_bits == 1);
}

void
test_app_satua_4 ()
{
  test_app_satua ("satua/satua4.c32sat", 1);
  assert (ext_approx_number_of_bits == 2);
}

void
test_app_satua_5 ()
{
  test_app_satua ("satua/satua5.c32sat", 1);
  assert (ext_approx_number_of_bits == 4);
}

void
test_app_satua_6 ()
{
  test_app_satua ("satua/satua6.c32sat", 0);
  assert (ext_approx_number_of_bits == 32);
}

void
test_app_satua_7 ()
{
  test_app_satua ("satua/satua7.c32sat", 1);
  assert (ext_approx_number_of_bits == 32);
}

void
test_app_satua_8 ()
{
  test_app_satua ("satua/satua8.c32sat", 0);
  assert (ext_approx_number_of_bits == 32);
}

void
test_app_satua_9 ()
{
  test_app_satua ("satua/satua9.c32sat", 0);
  assert (ext_approx_number_of_bits == 32);
}

void
test_app_satua_10 ()
{
  test_app_satua ("satua/satua10.c32sat", 0);
  assert (ext_approx_number_of_bits == 32);
}

void
test_app_unsat (char *file_name)
{
  FILE *output = tmpfile ();
  int argc = 5;
  char *argv[] =
    { app_name, "-s", "-no-ua", "-no-overflow", file_name };
  assert (c32sat_main
          (argc, argv, output, stderr) == ec_unsatisfiable);
  fclose (output);
}

void
test_app_unsat_1 ()
{
  test_app_unsat ("unsat/unsat1.c32sat");
}

void
test_app_unsat_2 ()
{
  test_app_unsat ("unsat/unsat2.c32sat");
}

void
test_app_unsat_3 ()
{
  test_app_unsat ("unsat/unsat3.c32sat");
}

void
test_app_unsat_4 ()
{
  test_app_unsat ("unsat/unsat4.c32sat");
}

void
test_app_unsat_5 ()
{
  test_app_unsat ("unsat/unsat5.c32sat");
}

void
test_app_unsat_6 ()
{
  test_app_unsat ("unsat/unsat6.c32sat");
}

void
test_app_unsat_7 ()
{
  test_app_unsat ("unsat/unsat7.c32sat");
}

void
test_app_unsat_8 ()
{
  test_app_unsat ("unsat/unsat8.c32sat");
}

void
test_app_unsat_9 ()
{
  test_app_unsat ("unsat/unsat9.c32sat");
}

void
test_app_unsat_10 ()
{
  test_app_unsat ("unsat/unsat10.c32sat");
}

void
test_app_unsat_11 ()
{
  test_app_unsat ("unsat/unsat11.c32sat");
}

void
test_app_unsat_12 ()
{
  test_app_unsat ("unsat/unsat12.c32sat");
}

void
test_app_unsat_13 ()
{
  test_app_unsat ("unsat/unsat13.c32sat");
}

void
test_app_unsat_14 ()
{
  test_app_unsat ("unsat/unsat14.c32sat");
}

void
test_app_unsat_15 ()
{
  test_app_unsat ("unsat/unsat15.c32sat");
}

void
test_app_unsat_16 ()
{
  test_app_unsat ("unsat/unsat16.c32sat");
}

void
test_app_unsat_17 ()
{
  test_app_unsat ("unsat/unsat17.c32sat");
}

void
test_app_taut (char *file_name)
{
  FILE *output = tmpfile ();
  int argc = 4;
  char *argv[] = { app_name, "-t", "-no-overflow", file_name };
  assert (c32sat_main
          (argc, argv, output, stderr) == ec_tautology);
  fclose (output);
}

void
test_app_taut_1 ()
{
  test_app_taut ("taut/taut1.c32sat");
}

void
test_app_taut_2 ()
{
  test_app_taut ("taut/taut2.c32sat");
}

void
test_app_taut_3 ()
{
  test_app_taut ("taut/taut3.c32sat");
}

void
test_app_taut_4 ()
{
  test_app_taut ("taut/taut4.c32sat");
}

void
test_app_taut_5 ()
{
  test_app_taut ("taut/taut5.c32sat");
}

void
test_app_taut_6 ()
{
  test_app_taut ("taut/taut6.c32sat");
}

void
test_app_taut_7 ()
{
  test_app_taut ("taut/taut7.c32sat");
}

void
test_app_taut_8 ()
{
  test_app_taut ("taut/taut8.c32sat");
}

void
test_app_taut_9 ()
{
  test_app_taut ("taut/taut9.c32sat");
}

void
test_app_taut_10 ()
{
  test_app_taut ("taut/taut10.c32sat");
}

void
test_app_taut_11 ()
{
  test_app_taut ("taut/taut11.c32sat");
}

void
test_app_taut_12 ()
{
  test_app_taut ("taut/taut12.c32sat");
}

void
test_app_taut_13 ()
{
  test_app_taut ("taut/taut13.c32sat");
}

void
test_app_taut_14 ()
{
  test_app_taut ("taut/taut14.c32sat");
}

void
test_app_taut_15 ()
{
  test_app_taut ("taut/taut15.c32sat");
}

void
test_app_taut_16 ()
{
  test_app_taut ("taut/taut16.c32sat");
}

void
test_app_taut_17 ()
{
  test_app_taut ("taut/taut17.c32sat");
}

void
test_app_taut_18 ()
{
  test_app_taut ("taut/taut18.c32sat");
}

void
test_app_taut_19 ()
{
  test_app_taut ("taut/taut19.c32sat");
}

void
test_app_taut_20 ()
{
  test_app_taut ("taut/taut20.c32sat");
}

void
test_app_taut_21 ()
{
  test_app_taut ("taut/taut21.c32sat");
}

void
test_app_taut_22 ()
{
  test_app_taut ("taut/taut22.c32sat");
}

void
test_app_taut_23 ()
{
  test_app_taut ("taut/taut23.c32sat");
}

void
test_app_taut_24 ()
{
  test_app_taut ("taut/taut24.c32sat");
}

void
test_app_taut_25 ()
{
  test_app_taut ("taut/taut25.c32sat");
}

void
test_app_taut_26 ()
{
  test_app_taut ("taut/taut26.c32sat");
}

void
test_app_taut_27 ()
{
  test_app_taut ("taut/taut27.c32sat");
}

void
test_app_taut_28 ()
{
  test_app_taut ("taut/taut28.c32sat");
}

void
test_app_taut_29 ()
{
  test_app_taut ("taut/taut29.c32sat");
}

void
test_app_taut_30 ()
{
  test_app_taut ("taut/taut30.c32sat");
}

void
test_app_taut_31 ()
{
  test_app_taut ("taut/taut31.c32sat");
}

void
test_app_no_taut (char *file_name)
{
  FILE *output = tmpfile ();
  int argc = 4;
  char *argv[] = { app_name, "-t", "-no-overflow", file_name };
  assert (c32sat_main
          (argc, argv, output, stderr) == ec_no_tautology);
  fclose (output);
}

void
test_app_no_taut_1 ()
{
  test_app_no_taut ("no_taut/no_taut1.c32sat");
}

void
test_app_no_taut_2 ()
{
  test_app_no_taut ("no_taut/no_taut2.c32sat");
}

void
test_app_no_taut_3 ()
{
  test_app_no_taut ("no_taut/no_taut3.c32sat");
}

void
test_app_no_taut_4 ()
{
  test_app_no_taut ("no_taut/no_taut4.c32sat");
}

void
test_app_no_taut_5 ()
{
  test_app_no_taut ("no_taut/no_taut5.c32sat");
}

void
test_app_no_taut_6 ()
{
  test_app_no_taut ("no_taut/no_taut6.c32sat");
}

void
test_app_no_taut_7 ()
{
  test_app_no_taut ("no_taut/no_taut7.c32sat");
}

void
test_app_no_taut_8 ()
{
  test_app_no_taut ("no_taut/no_taut8.c32sat");
}

void
test_app_no_taut_9 ()
{
  test_app_no_taut ("no_taut/no_taut9.c32sat");
}

void
test_app_no_taut_10 ()
{
  test_app_no_taut ("no_taut/no_taut10.c32sat");
}

void
test_app_no_taut_11 ()
{
  test_app_no_taut ("no_taut/no_taut11.c32sat");
}

void
test_app_no_taut_12 ()
{
  test_app_no_taut ("no_taut/no_taut12.c32sat");
}

void
test_app_always_def (char *file_name)
{
  FILE *output = tmpfile ();
  int argc = 4;
  char *argv[] = { app_name, "-ad", "-no-overflow", file_name };
  assert (c32sat_main
          (argc, argv, output, stderr) == ec_always_defined);
  fclose (output);
}

void
test_app_always_def1 ()
{
  test_app_always_def ("always_def/always_def1.c32sat");
}

void
test_app_always_def2 ()
{
  test_app_always_def ("always_def/always_def2.c32sat");
}

void
test_app_always_def3 ()
{
  test_app_always_def ("always_def/always_def3.c32sat");
}

void
test_app_always_def4 ()
{
  test_app_always_def ("always_def/always_def4.c32sat");
}

void
test_app_always_def5 ()
{
  test_app_always_def ("always_def/always_def5.c32sat");
}

void
test_app_always_def6 ()
{
  test_app_always_def ("always_def/always_def6.c32sat");
}

void
test_app_always_def7 ()
{
  test_app_always_def ("always_def/always_def7.c32sat");
}

void
test_app_always_def8 ()
{
  test_app_always_def ("always_def/always_def8.c32sat");
}

void
test_app_always_def9 ()
{
  test_app_always_def ("always_def/always_def9.c32sat");
}

void
test_app_always_def10 ()
{
  test_app_always_def ("always_def/always_def10.c32sat");
}

void
test_app_always_def11 ()
{
  test_app_always_def ("always_def/always_def11.c32sat");
}

void
test_app_always_def12 ()
{
  test_app_always_def ("always_def/always_def12.c32sat");
}

void
test_app_always_def13 ()
{
  test_app_always_def ("always_def/always_def13.c32sat");
}

void
test_app_always_def14 ()
{
  test_app_always_def ("always_def/always_def14.c32sat");
}

void
test_app_not_always_def (char *file_name)
{
  FILE *output = tmpfile ();
  int argc = 4;
  char *argv[] = { app_name, "-ad", "-no-overflow", file_name };
  assert (c32sat_main
          (argc, argv, output, stderr) == ec_not_always_defined);
  fclose (output);
}

void
test_app_not_always_def1 ()
{
  test_app_not_always_def ("not_always_def/not_always_def1.c32sat");
}

void
test_app_not_always_def2 ()
{
  test_app_not_always_def ("not_always_def/not_always_def2.c32sat");
}

void
test_app_not_always_def3 ()
{
  test_app_not_always_def ("not_always_def/not_always_def3.c32sat");
}

void
test_app_not_always_def4 ()
{
  test_app_not_always_def ("not_always_def/not_always_def4.c32sat");
}

void
test_app_not_always_def5 ()
{
  test_app_not_always_def ("not_always_def/not_always_def5.c32sat");
}

void
test_app_not_always_def6 ()
{
  test_app_not_always_def ("not_always_def/not_always_def6.c32sat");
}

void
test_app_not_always_def7 ()
{
  test_app_not_always_def ("not_always_def/not_always_def7.c32sat");
}

void
test_app_not_always_def8 ()
{
  test_app_not_always_def ("not_always_def/not_always_def8.c32sat");
}

void
test_app_not_always_def9 ()
{
  test_app_not_always_def ("not_always_def/not_always_def9.c32sat");
}

void
test_app_not_always_def10 ()
{
  test_app_not_always_def ("not_always_def/not_always_def10.c32sat");
}

void
test_app_not_always_def11 ()
{
  test_app_not_always_def ("not_always_def/not_always_def11.c32sat");
}

void
test_app_not_always_def12 ()
{
  test_app_not_always_def ("not_always_def/not_always_def12.c32sat");
}

void
test_app_always_undef (char *file_name)
{
  FILE *output = tmpfile ();
  int argc = 4;
  char *argv[] = { app_name, "-au", "-no-overflow", file_name };
  assert (c32sat_main
          (argc, argv, output, stderr) == ec_always_undefined);
  fclose (output);
}

void
test_app_always_undef1 ()
{
  test_app_always_undef ("always_undef/always_undef1.c32sat");
}

void
test_app_always_undef2 ()
{
  test_app_always_undef ("always_undef/always_undef2.c32sat");
}

void
test_app_always_undef3 ()
{
  test_app_always_undef ("always_undef/always_undef3.c32sat");
}

void
test_app_always_undef4 ()
{
  test_app_always_undef ("always_undef/always_undef4.c32sat");
}

void
test_app_always_undef5 ()
{
  test_app_always_undef ("always_undef/always_undef5.c32sat");
}

void
test_app_always_undef6 ()
{
  test_app_always_undef ("always_undef/always_undef6.c32sat");
}

void
test_app_always_undef7 ()
{
  test_app_always_undef ("always_undef/always_undef7.c32sat");
}

void
test_app_always_undef8 ()
{
  test_app_always_undef ("always_undef/always_undef8.c32sat");
}

void
test_app_always_undef9 ()
{
  test_app_always_undef ("always_undef/always_undef9.c32sat");
}

void
test_app_always_undef10 ()
{
  test_app_always_undef ("always_undef/always_undef10.c32sat");
}

void
test_app_not_always_undef (char *file_name)
{
  FILE *output = tmpfile ();
  int argc = 4;
  char *argv[] = { app_name, "-au", "-no-overflow", file_name };
  assert (c32sat_main
          (argc, argv, output, stderr) == ec_not_always_undefined);
  fclose (output);
}

void
test_app_not_always_undef1 ()
{
  test_app_not_always_undef ("not_always_undef/not_always_undef1.c32sat");
}

void
test_app_not_always_undef2 ()
{
  test_app_not_always_undef ("not_always_undef/not_always_undef2.c32sat");
}

void
test_app_not_always_undef3 ()
{
  test_app_not_always_undef ("not_always_undef/not_always_undef3.c32sat");
}

void
test_app_not_always_undef4 ()
{
  test_app_not_always_undef ("not_always_undef/not_always_undef4.c32sat");
}

void
test_app_not_always_undef5 ()
{
  test_app_not_always_undef ("not_always_undef/not_always_undef5.c32sat");
}

void
test_app_not_always_undef6 ()
{
  test_app_not_always_undef ("not_always_undef/not_always_undef6.c32sat");
}

void
test_app_not_always_undef7 ()
{
  test_app_not_always_undef ("not_always_undef/not_always_undef7.c32sat");
}

void
test_app_not_always_undef8 ()
{
  test_app_not_always_undef ("not_always_undef/not_always_undef8.c32sat");
}

void
test_app_not_always_undef9 ()
{
  test_app_not_always_undef ("not_always_undef/not_always_undef9.c32sat");
}

void
test_app_not_always_undef10 ()
{
  test_app_not_always_undef ("not_always_undef/not_always_undef10.c32sat");
}


void
run_app_tests ()
{
  run_test (test_app_error_invalid_usage);
  check_output ("output/app_error_invalid_usage_expected.txt",
                "output/app_error_invalid_usage_output.txt");
  run_test (test_app_error_invalid_usage_unknown_option);
  check_output ("output/app_error_invalid_usage_unknown_option_expected.txt",
                "output/app_error_invalid_usage_unknown_option_output.txt");
  run_test (test_app_error_io_error);
  check_output ("output/app_error_io_error_expected.txt",
                "output/app_error_io_error_output.txt");
  run_test (test_app_error_build_parse_tree_error);
  check_output ("output/app_error_build_parse_tree_error_expected.txt",
                "output/app_error_build_parse_tree_error_output.txt");
  test_app_error_invalid_under_approx_width1();
  check_output ("output/app_error_invalid_under_approx_width1_expected.txt",
                "output/app_error_invalid_under_approx_width1_output.txt");
  test_app_error_invalid_under_approx_width2();
  check_output ("output/app_error_invalid_under_approx_width2_expected.txt",
                "output/app_error_invalid_under_approx_width2_output.txt");
  test_app_error_invalid_under_approx_width3();
  check_output ("output/app_error_invalid_under_approx_width3_expected.txt",
                "output/app_error_invalid_under_approx_width3_output.txt");
  test_app_error_dump_no_under_approx_width1();
  check_output ("output/app_error_dump_no_under_approx_width1_expected.txt",
                "output/app_error_dump_no_under_approx_width1_output.txt");
  test_app_error_dump_no_under_approx_width2();
  check_output ("output/app_error_dump_no_under_approx_width2_expected.txt",
                "output/app_error_dump_no_under_approx_width2_output.txt");
  run_test (test_app_pretty_print_formula1);
  check_output ("output/pp_formula1_expected.txt",
                "output/pp_formula1_output.txt");
  run_test (test_app_pretty_print_formula2);
  check_output ("output/pp_formula2_expected.txt",
                "output/pp_formula2_output.txt");
  run_test (test_app_pretty_print_formula3);
  check_output ("output/pp_formula3_expected.txt",
                "output/pp_formula3_output.txt");
  run_test (test_app_pretty_print_formula4);
  check_output ("output/pp_formula4_expected.txt",
                "output/pp_formula4_output.txt");
  run_test (test_app_pretty_print_ignore_other_options);
  check_output ("output/pp_formula1_expected.txt",
                "output/pp_formula1_output.txt");
  run_test (test_app_error_too_many_variables);
  check_output ("output/app_error_too_many_variables_expected.txt",
                "output/app_error_too_many_variables_output.txt");
  run_test (test_app_error_parse_tree_analysis_too_many_aigs);
  check_output
    ("output/app_error_parse_tree_analysis_too_many_aigs_expected.txt",
     "output/app_error_parse_tree_analysis_too_many_aigs_output.txt");
  run_test (test_app_error_aig_too_many_aigs);
  check_output ("output/app_error_aig_too_many_aigs_expected.txt",
                "output/app_error_aig_too_many_aigs_output.txt");
  run_test (test_app_error_too_many_cnf_clauses);
  check_output ("output/app_error_too_many_cnf_clauses_expected.txt",
                "output/app_error_too_many_cnf_clauses_output.txt");
  run_test (test_app_help);
  run_test (test_app_help_ignore_other_options);
  run_test (test_app_return_dump_aig_1);
  run_test (test_app_return_dump_aig_2);
  run_test (test_app_return_dump_aig_3);
  run_test (test_app_return_dump_cnf_1);
  run_test (test_app_return_dump_cnf_2);
  run_test (test_app_return_dump_cnf_3);
  run_test (test_app_sat_1);
  run_test (test_app_sat_2);
  run_test (test_app_sat_3);
  run_test (test_app_sat_4);
  run_test (test_app_sat_5);
  run_test (test_app_sat_6);
  run_test (test_app_sat_7);
  run_test (test_app_sat_8);
  run_test (test_app_sat_9);
  run_test (test_app_sat_10);
  run_test (test_app_sat_11);
  run_test (test_app_sat_12);
  run_test (test_app_sat_13);
  run_test (test_app_sat_14);
  run_test (test_app_sat_15);
  run_test (test_app_sat_16);
  run_test (test_app_sat_17);
  run_test (test_app_sat_18);
  run_test (test_app_sat_19);
  run_test (test_app_satua_1);
  run_test (test_app_satua_2);
  run_test (test_app_satua_3);
  run_test (test_app_satua_4);
  run_test (test_app_satua_5);
  run_test (test_app_satua_6);
  run_test (test_app_satua_7);
  run_test (test_app_satua_8);
  run_test (test_app_satua_9);
  run_test (test_app_satua_10);
  run_test (test_app_unsat_1);
  run_test (test_app_unsat_2);
  run_test (test_app_unsat_3);
  run_test (test_app_unsat_4);
  run_test (test_app_unsat_5);
  run_test (test_app_unsat_6);
  run_test (test_app_unsat_7);
  run_test (test_app_unsat_8);
  run_test (test_app_unsat_9);
  run_test (test_app_unsat_10);
  run_test (test_app_unsat_11);
  run_test (test_app_unsat_12);
  run_test (test_app_unsat_13);
  run_test (test_app_unsat_14);
  run_test (test_app_unsat_15);
  run_test (test_app_unsat_16);
  run_test (test_app_unsat_17);
  run_test (test_app_taut_1);
  run_test (test_app_taut_2);
  run_test (test_app_taut_3);
  run_test (test_app_taut_4);
  run_test (test_app_taut_5);
  run_test (test_app_taut_6);
  run_test (test_app_taut_7);
  run_test (test_app_taut_8);
  run_test (test_app_taut_9);
  run_test (test_app_taut_10);
  run_test (test_app_taut_11);
  run_test (test_app_taut_12);
  run_test (test_app_taut_13);
  run_test (test_app_taut_14);
  run_test (test_app_taut_15);
  run_test (test_app_taut_16);
  run_test (test_app_taut_17);
  run_test (test_app_taut_18);
  run_test (test_app_taut_19);
  run_test (test_app_taut_20);
  run_test (test_app_taut_21);
  run_test (test_app_taut_22);
  run_test (test_app_taut_23);
  run_test (test_app_taut_24);
  run_test (test_app_taut_25);
  run_test (test_app_taut_26);
  run_test (test_app_taut_27);
  run_test (test_app_taut_28);
  run_test (test_app_taut_29);
  run_test (test_app_taut_30);
  run_test (test_app_taut_31);
  run_test (test_app_no_taut_1);
  run_test (test_app_no_taut_2);
  run_test (test_app_no_taut_3);
  run_test (test_app_no_taut_4);
  run_test (test_app_no_taut_5);
  run_test (test_app_no_taut_6);
  run_test (test_app_no_taut_7);
  run_test (test_app_no_taut_8);
  run_test (test_app_no_taut_9);
  run_test (test_app_no_taut_10);
  run_test (test_app_no_taut_11);
  run_test (test_app_no_taut_12);
  run_test (test_app_always_def1);
  run_test (test_app_always_def2);
  run_test (test_app_always_def3);
  run_test (test_app_always_def4);
  run_test (test_app_always_def5);
  run_test (test_app_always_def6);
  run_test (test_app_always_def7);
  run_test (test_app_always_def8);
  run_test (test_app_always_def9);
  run_test (test_app_always_def10);
  run_test (test_app_always_def11);
  run_test (test_app_always_def12);
  run_test (test_app_always_def13);
  run_test (test_app_always_def14);
  run_test (test_app_not_always_def1);
  run_test (test_app_not_always_def2);
  run_test (test_app_not_always_def3);
  run_test (test_app_not_always_def4);
  run_test (test_app_not_always_def5);
  run_test (test_app_not_always_def6);
  run_test (test_app_not_always_def7);
  run_test (test_app_not_always_def8);
  run_test (test_app_not_always_def9);
  run_test (test_app_not_always_def10);
  run_test (test_app_not_always_def11);
  run_test (test_app_not_always_def12);
  run_test (test_app_always_undef1);
  run_test (test_app_always_undef2);
  run_test (test_app_always_undef3);
  run_test (test_app_always_undef4);
  run_test (test_app_always_undef5);
  run_test (test_app_always_undef6);
  run_test (test_app_always_undef7);
  run_test (test_app_always_undef8);
  run_test (test_app_always_undef9);
  run_test (test_app_always_undef10);
  run_test (test_app_not_always_undef1);
  run_test (test_app_not_always_undef2);
  run_test (test_app_not_always_undef3);
  run_test (test_app_not_always_undef4);
  run_test (test_app_not_always_undef5);
  run_test (test_app_not_always_undef6);
  run_test (test_app_not_always_undef7);
  run_test (test_app_not_always_undef8);
  run_test (test_app_not_always_undef9);
  run_test (test_app_not_always_undef10);
}
