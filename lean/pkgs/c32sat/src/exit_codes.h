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
#ifndef _EXIT_CODES_
#define _EXIT_CODES_

enum ExitCode
{
  /** The pretty printing succeeded */
  ec_pretty_print_success = 0,
  /** The help message was printed */
  ec_help_success,
  /** The formula is satisfiable */
  ec_satisfiable,
  /** The formula is unsatisfiable */
  ec_unsatisfiable,
  /** The formula is a tautology */
  ec_tautology,
  /** The formula is no tautology */
  ec_no_tautology,
  /** The result of the formula is always defined (C99) */
  ec_always_defined,
  /** The result of the formula io not always defined (C99)  */
  ec_not_always_defined,
  /** The result of the expression is always undefined (C99) */
  ec_always_undefined,
  /** The result of the expression is not always undefined (C99) */
  ec_not_always_undefined,
  /** The aig dumping succeeded */
  ec_dump_aig_success,
  /** The cnf dumping succeeded */
  ec_dump_cnf_success,
  /** An error occured while building the parse tree */
  ec_build_parse_tree_error,
  /** C32SAT was called in an invalid way */
  ec_invalid_usage,
  /** An IO error occured */
  ec_io_error,
  /** Out of memory */
  ec_out_of_memory,
  /** A SAT solver error occured */
  ec_sat_solver_error,
  /** Too many variables in the input formula */
  ec_too_many_variables,
  /** Too many AIGs */
  ec_too_many_aigs,
  /** Too many CNF clauses */
  ec_too_many_cnf_clauses
};

typedef enum ExitCode ExitCode;

#endif
