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
#ifndef _ERROR_MANAGEMENT_H_
#define _ERROR_MANAGEMENT_H_

#include <stdio.h>
#include "bool.h"

/* Determines if there are too many variables in the parse tree.
 * See @ref ext_number_of_supported_variables. */
extern Bool ext_too_many_variables_error_occured;
/** Determines if too many AIGs should have been created.
 * See @ref ext_number_of_supported_aigs. */
extern Bool ext_too_many_aigs_error_occured;

/** Represents all possible kinds of errors. */
enum ErrorKind
{
  e_memory_management_out_of_memory = 0,
  /** Invalid char */
  e_scanner_invalid_char,
  /** Too big integer */
  e_scanner_int_too_big,
  /** Ident has too many characters */
  e_scanner_ident_too_long,
  /** Integer has leading zero(s) */
  e_scanner_lead_zero,
  /** Used "=" instead of "==" */
  e_scanner_invalid_equal,
  /** Syntactical parse error */
  e_parser_invalid_token,
  /** Invalid usage of the main function */
  e_app_invalid_usage,
  /** An unknown option was used */
  e_app_invalid_usage_unknown_option,
  /** An input error occured */
  e_app_input_error,
  /** An output error occured */
  e_app_output_error,
  /** SAT Solver error occured */
  e_app_sat_solver_error,
  /** Invalid under-approximation width */
  e_app_invalid_under_approx_width,
  /** No under-approximation width was specified for dumping */
  e_app_dump_no_under_approx_width,
  /** Too many variables */
  e_parse_tree_analysis_too_many_variables,
  /** Too many AIGs */
  e_aig_too_many_aigs,
  /** Too many CNF clauses */
  e_cnf_too_many_cnf_clauses
};

typedef enum ErrorKind ErrorKind;

/** Inits the error management.
 * @param err_output The file used for printing error messages
 */
void init_error_management (FILE * err_output);

/** Checks if error management is initialised.
 * @return @ref b_true if initialised and @ref b_false if not
 */
Bool is_initialised_error_management ();

/** Checks if an error has occured.
 *  @return @ref b_true if an error has occured and @ref b_false if not
 */
Bool has_error_occured ();

/** Resets all error states.
 */
void reset_errors ();

/** Prints an error message to the error output which was specified
 * by calling @ref init_error_management.
 * @param kind The kind of error which occured
 * @param line The corresponding line of the error in the input file
 * @param col The corresponding column of the error in the input file
 * @param param Some error cases need an integer parameter
 * @param str_param Some error cases need a string parameter
 */
void error (ErrorKind kind, unsigned int line,
            unsigned int col, int param, const char *str_param);

#endif
