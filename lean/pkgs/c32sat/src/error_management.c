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
#include <string.h>
#include <stdlib.h>
#include "error_management.h"
#include "bool.h"
#include "symbol.h"
#include "token.h"
#include "config.h"
#include "scanner.h"

Bool ext_too_many_variables_error_occured;
Bool ext_too_many_aigs_error_occured;

FILE *g_err_output;
Bool g_error_occured;
Bool g_initialised_error_management = b_false;

static const char *msg_memory_manager_out_of_memory = "Out of memory";
static const char *msg_scanner_invalid_char = "Invalid character: ";
static const char *msg_scanner_invald_newline = "Invalid newline";
static const char *msg_scanner_int_too_big = "Integer constant is too big: ";
static const char *msg_scanner_ident_too_long = "Identifier is too long: ";
static const char *msg_scanner_lead_zero = "Leading zero is not allowed: ";
static const char *msg_scanner_unexpected_eof = "Unexpected end of input";
static const char *msg_parser_invalid_token = "Parse error at token ";
static const char *msg_parser_invalid_token_eof =
  "Parse error at end of input";
static const char *msg_app_unknown_option = "Unknown option ";
static const char *msg_app_input_error = "Cannot open file ";
static const char *msg_app_output_error = "Cannot write to file ";
static const char *msg_app_sat_solver_error =
  "SAT solver error occurred! Error number: ";
static const char *msg_parse_tree_analysis_too_many_variables =
  "Too many variables! Maximum number of variables is ";
static const char *msg_aig_too_many_aigs =
  "Too many AIGs have been generated! Maximum number of AIGs is ";
static const char *msg_cnf_too_many_cnf_clauses =
  "Too many CNF clauses have been generated! Maximum number of CNF clauses is ";
static const char *msg_app_invalid_under_approx_width =
  "Invalid under-approximation width!\n    Width must be a power of two and less than number of bits!";
static const char *msg_app_dump_no_under_approx_width =
"No under-approximation width has been specified for dumping!\n    Please use \"-ua-width <width>\" or disable under-approximation with \"-no-ua\"!";

static const char *hint_scanner_invalid_equal = "    '=' expected";

void
init_error_management (FILE * err_output)
{
  assert (err_output != NULL);
  g_err_output = err_output;
  g_initialised_error_management = b_true;
  reset_errors ();
}

Bool
is_initialised_error_management ()
{
  return g_initialised_error_management;
}

Bool
has_error_occured ()
{
  assert (is_initialised_error_management ());
  return g_error_occured;
}

void
reset_errors ()
{
  assert (is_initialised_error_management ());
  ext_too_many_variables_error_occured = b_false;
  ext_too_many_aigs_error_occured = b_false;
  g_error_occured = b_false;
}

void
error (ErrorKind kind, unsigned int line,
       unsigned int col, int param, const char *str_param)
{
  assert (is_initialised_error_management ());
  g_error_occured = b_true;
  fprintf (g_err_output, "==> ");
  switch (kind)
    {
    case e_memory_management_out_of_memory:
      fprintf (g_err_output, "%s\n", msg_memory_manager_out_of_memory);
      break;
    case e_scanner_invalid_char:
      assert (line > 0 && col > 0);
      fprintf (g_err_output, "%u:%u: %s'%c'\n", line, col,
               msg_scanner_invalid_char, param);
      break;
    case e_scanner_int_too_big:
      assert (line > 0 && col > 0);
      if (param)
        {
          fprintf (g_err_output, "%u:%u: %s%s\n", line, col,
                   msg_scanner_int_too_big, str_param);
        }
      else
        {
          fprintf (g_err_output, "%u:%u: %s%s...\n", line, col,
                   msg_scanner_int_too_big, str_param);
        }
      break;
    case e_scanner_ident_too_long:
      assert (line > 0 && col > 0);
      fprintf (g_err_output, "%u:%u: %s%s...\n", line, col,
               msg_scanner_ident_too_long, str_param);
      break;
    case e_scanner_lead_zero:
      assert (line > 0 && col > 0);
      if (((ext_number_of_bits == 32) && (param > MAX_INT_STRING_LENGTH_32))
          || ((ext_number_of_bits == 16)
              && (param > MAX_INT_STRING_LENGTH_16))
          || ((ext_number_of_bits == 8) && (param > MAX_INT_STRING_LENGTH_8)))
        {
          fprintf (g_err_output, "%u:%u: %s%s...\n", line, col,
                   msg_scanner_lead_zero, str_param);
        }
      else
        {
          fprintf (g_err_output, "%u:%u: %s%s\n", line, col,
                   msg_scanner_lead_zero, str_param);
        }
      break;
    case e_scanner_invalid_equal:
      assert (line > 0 && col > 0);
      switch (param)
        {
        case EOF:
          fprintf (g_err_output, "%s\n%s\n", msg_scanner_unexpected_eof,
                   hint_scanner_invalid_equal);
          break;
        case 10:               /* Newline */
          fprintf (g_err_output, "%u:%u: %s\n%s\n", line, col,
                   msg_scanner_invald_newline, hint_scanner_invalid_equal);
          break;
        default:
          fprintf (g_err_output, "%u:%u: %s'%c'\n%s\n", line, col,
                   msg_scanner_invalid_char, param,
                   hint_scanner_invalid_equal);
          break;
        }
      break;
    case e_parser_invalid_token:
      assert (line > 0 && col > 0);
      if (strcmp (str_param, get_token_symbol (t_eof)) == 0)
        {
          fprintf (g_err_output, "%s\n", msg_parser_invalid_token_eof);
        }
      else
        {
          fprintf (g_err_output, "%u:%u: %s\"%s\"\n", line, col,
                   msg_parser_invalid_token, str_param);
        }
      break;
    case e_app_invalid_usage:
      fprintf (g_err_output, "%s\n", str_param);
      break;
    case e_app_invalid_usage_unknown_option:
      fprintf (g_err_output, "%s\"%s\"\n", msg_app_unknown_option, str_param);
      break;
    case e_app_input_error:
      fprintf (g_err_output, "%s\"%s\"\n", msg_app_input_error, str_param);
      break;
    case e_app_output_error:
      fprintf (g_err_output, "%s\"%s\"\n", msg_app_output_error, str_param);
      break;
    case e_app_sat_solver_error:
      fprintf (g_err_output, "%s%d\n", msg_app_sat_solver_error, param);
      break;
    case e_app_invalid_under_approx_width:
      fprintf (g_err_output, "%s\n", msg_app_invalid_under_approx_width);
      break;
    case e_app_dump_no_under_approx_width:
      fprintf (g_err_output, "%s\n", msg_app_dump_no_under_approx_width);
      break;
    case e_parse_tree_analysis_too_many_variables:
      fprintf (g_err_output, "%s%d\n",
               msg_parse_tree_analysis_too_many_variables, param);
      ext_too_many_variables_error_occured = b_true;
      break;
    case e_aig_too_many_aigs:
      fprintf (g_err_output, "%s%d\n", msg_aig_too_many_aigs, param);
      ext_too_many_aigs_error_occured = b_true;
      break;
    case e_cnf_too_many_cnf_clauses:
      fprintf (g_err_output, "%s%d\n", msg_cnf_too_many_cnf_clauses, param);
      break;
    }
}
