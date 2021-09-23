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
#include "error_management_test.h"
#include "test_logging.h"
#include "../bool.h"
#include "../symbol.h"
#include "../token.h"
#include "../error_management.h"

void
test_init_error_management ()
{
  FILE *output = fopen ("output/error_management_errors_output.txt", "w");
  assert (!is_initialised_error_management ());
  init_error_management (output);
  assert (!has_error_occured ());
  fclose (output);
}

void
test_error_and_reset_errors ()
{
  FILE *output = fopen ("output/error_management_errors_output.txt", "w");
  init_error_management (output);
  assert (!has_error_occured ());
  error (e_memory_management_out_of_memory, 0, 0, 0, NULL);
  assert (has_error_occured ());
  error (e_scanner_invalid_char, 1, 1, '$', NULL);
  assert (has_error_occured ());
  error (e_scanner_int_too_big, 2, 1, b_false, "2147483647");
  assert (has_error_occured ());
  error (e_scanner_int_too_big, 4, 2, b_true, "2147483653");
  error (e_scanner_ident_too_long, 10, 23, 0,
         "xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx");
  error (e_scanner_lead_zero, 17, 4, 2, "003");
  error (e_scanner_lead_zero, 18, 1, 100, "0123123123");
  error (e_scanner_invalid_equal, 5, 2, 'a', NULL);
  error (e_scanner_invalid_equal, 5, 2, 10, NULL);
  error (e_scanner_invalid_equal, 5, 2, EOF, NULL);
  error (e_parser_invalid_token, 4, 5, 0, "param1");
  error (e_parser_invalid_token, 5, 5, 0, get_token_symbol (t_eof));
  error (e_app_invalid_usage, 0, 0, 0, "Usage message");
  error (e_app_invalid_under_approx_width, 0, 0, 0, "message");
  error (e_app_dump_no_under_approx_width, 0, 0, 0, "message");
  error (e_app_invalid_usage_unknown_option, 0, 0, 0, "-x");
  error (e_app_input_error, 0, 0, 0, "input.txt");
  error (e_app_output_error, 0, 0, 0, "output.txt");
  error (e_app_sat_solver_error, 0, 0, -1, NULL);
  assert (!ext_too_many_variables_error_occured);
  error (e_parse_tree_analysis_too_many_variables, 0, 0, 2000000000, NULL);
  assert (ext_too_many_variables_error_occured);
  assert (!ext_too_many_aigs_error_occured);
  error (e_aig_too_many_aigs, 0, 0, 1000, NULL);
  assert (ext_too_many_aigs_error_occured);
  error (e_cnf_too_many_cnf_clauses, 0, 0, 2000, NULL);
  reset_errors ();
  assert (!has_error_occured ());
  assert (!ext_too_many_variables_error_occured);
  assert (!ext_too_many_aigs_error_occured);
  fclose (output);
}

void
run_error_management_tests ()
{
  run_test (test_init_error_management);
  run_test (test_error_and_reset_errors);
  check_output ("output/error_management_errors_expected.txt",
                "output/error_management_errors_output.txt");
}
