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
#include <stdio.h>
#include <string.h>
#include "scanner_test.h"
#include "test_logging.h"
#include "../token.h"
#include "../memory_management.h"
#include "../error_management.h"
#include "../scanner.h"
#include "../config.h"

Bool
equals_token (const Token * token1, const Token * token2)
{
  assert (token1 != NULL && token2 != NULL);
  if (token1->kind == token2->kind && token1->line == token2->line
      && token1->col == token2->col)
    {
      if (token1->kind == t_ident)
        {
          assert (token1->str != NULL && token2->str != NULL);
          return strcmp (token1->str, token2->str) == 0 ? b_true : b_false;
        }
      else if (token1->kind == t_integer)
        {
          return token1->val == token2->val;
        }
      return b_true;
    }
  return b_false;
}

void
set_token (Token * expected, int kind, int line, int col, char *str, int val)
{
  expected->kind = kind;
  expected->line = line;
  expected->col = col;
  expected->str = str;
  expected->val = val;
}

int
scan_check_delete (Scanner * scanner, Token * expected)
{
  Token *result = scan (scanner);
  int return_val = equals_token (result, expected);
  delete_token (result);
  return return_val;
}

void
test_create_delete_scanner ()
{
  FILE *input = fopen ("input/formula1.c32sat", "r");
  Scanner *scanner = NULL;
  assert (ext_number_of_bits == 32);
  init_error_management (stderr);
  init_memory_management ();
  scanner = create_scanner (input);
  assert (scanner->input == input);
  assert (scanner->cur == 'x');
  assert (scanner->line == 1);
  assert (scanner->col == 1);
  assert (scanner->max_int_val == MAX_INT_VAL_32);
  assert (scanner->max_int_string_length == MAX_INT_STRING_LENGTH_32);
  delete_scanner (scanner);
  finalise_memory_management ();
  fclose (input);
}

void
test_scan_all_tokens (char *input)
{
  /* init */
  FILE *finput = fopen (input, "r");
  Token expected;
  Scanner *scanner = NULL;
  assert (ext_number_of_bits == 32);
  init_error_management (stderr);
  init_memory_management ();
  scanner = create_scanner (finput);
  /* start test */
  /* ident */
  set_token (&expected, t_ident, 1, 1, "state02", 0);
  assert (scan_check_delete (scanner, &expected));
  set_token (&expected, t_ident, 1, 9, "ident34", 0);
  assert (scan_check_delete (scanner, &expected));
  set_token (&expected, t_ident, 1, 17, "name_9", 0);
  assert (scan_check_delete (scanner, &expected));
  set_token (&expected, t_ident, 1, 24, "test", 0);
  assert (scan_check_delete (scanner, &expected));
  set_token (&expected, t_ident, 1, 29, "heat", 0);
  assert (scan_check_delete (scanner, &expected));
  set_token (&expected, t_ident, 1, 34, "close", 0);
  assert (scan_check_delete (scanner, &expected));
  set_token (&expected, t_ident, 1, 40, "x_y", 0);
  assert (scan_check_delete (scanner, &expected));
  set_token (&expected, t_ident, 1, 44, "x", 0);
  assert (scan_check_delete (scanner, &expected));
  set_token (&expected, t_ident, 1, 46, "_", 0);
  assert (scan_check_delete (scanner, &expected));
  set_token (&expected, t_ident, 1, 48, "_x_", 0);
  assert (scan_check_delete (scanner, &expected));
  set_token (&expected, t_ident, 1, 52, "__3", 0);
  assert (scan_check_delete (scanner, &expected));
  /* test longest possible identifier: */
  set_token (&expected, t_ident, 2, 1,
             "xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx",
             0);
  assert (scan_check_delete (scanner, &expected));
  /* comment */
  /* integer */
  set_token (&expected, t_integer, 4, 1, NULL, 23);
  assert (scan_check_delete (scanner, &expected));
  set_token (&expected, t_integer, 4, 4, NULL, 7890);
  assert (scan_check_delete (scanner, &expected));
  set_token (&expected, t_integer, 4, 9, NULL, 43245);
  assert (scan_check_delete (scanner, &expected));
  set_token (&expected, t_integer, 4, 15, NULL, 45324);
  assert (scan_check_delete (scanner, &expected));
  set_token (&expected, t_integer, 4, 21, NULL, 3);
  assert (scan_check_delete (scanner, &expected));
  set_token (&expected, t_integer, 4, 23, NULL, 0);
  assert (scan_check_delete (scanner, &expected));
  /* test biggest possible 32 bit int */
  set_token (&expected, t_integer, 4, 25, NULL, MAX_INT_VAL_32);
  assert (scan_check_delete (scanner, &expected));
  /* ( ) */
  set_token (&expected, t_lpar, 5, 1, NULL, 0);
  assert (scan_check_delete (scanner, &expected));
  set_token (&expected, t_rpar, 5, 10, NULL, 0);
  assert (scan_check_delete (scanner, &expected));
  /* => <=> */
  set_token (&expected, t_imp, 6, 1, NULL, 0);
  assert (scan_check_delete (scanner, &expected));
  set_token (&expected, t_dimp, 6, 4, NULL, 0);
  assert (scan_check_delete (scanner, &expected));
  /* ? : */
  set_token (&expected, t_qm, 7, 1, NULL, 0);
  assert (scan_check_delete (scanner, &expected));
  set_token (&expected, t_colon, 7, 3, NULL, 0);
  assert (scan_check_delete (scanner, &expected));
  /* || && */
  set_token (&expected, t_or, 8, 1, NULL, 0);
  assert (scan_check_delete (scanner, &expected));
  set_token (&expected, t_and, 8, 4, NULL, 0);
  assert (scan_check_delete (scanner, &expected));
  /* == != */
  set_token (&expected, t_eq, 9, 1, NULL, 0);
  assert (scan_check_delete (scanner, &expected));
  set_token (&expected, t_neq, 9, 4, NULL, 0);
  assert (scan_check_delete (scanner, &expected));
  /* < <= > >= */
  set_token (&expected, t_lt, 10, 1, NULL, 0);
  assert (scan_check_delete (scanner, &expected));
  set_token (&expected, t_lte, 10, 3, NULL, 0);
  assert (scan_check_delete (scanner, &expected));
  set_token (&expected, t_gt, 10, 6, NULL, 0);
  assert (scan_check_delete (scanner, &expected));
  set_token (&expected, t_gte, 10, 8, NULL, 0);
  assert (scan_check_delete (scanner, &expected));
  /* >> << */
  set_token (&expected, t_shiftr, 11, 1, NULL, 0);
  assert (scan_check_delete (scanner, &expected));
  set_token (&expected, t_shiftl, 11, 4, NULL, 0);
  assert (scan_check_delete (scanner, &expected));
  /* + - */
  set_token (&expected, t_plus, 12, 1, NULL, 0);
  assert (scan_check_delete (scanner, &expected));
  set_token (&expected, t_minus, 12, 3, NULL, 0);
  assert (scan_check_delete (scanner, &expected));
  /* * / % */
  set_token (&expected, t_mult, 13, 1, NULL, 0);
  assert (scan_check_delete (scanner, &expected));
  set_token (&expected, t_div, 13, 3, NULL, 0);
  assert (scan_check_delete (scanner, &expected));
  set_token (&expected, t_mod, 13, 5, NULL, 0);
  assert (scan_check_delete (scanner, &expected));
  /* ! ~ INT_MAX INT_MIN */
  set_token (&expected, t_not, 14, 1, NULL, 0);
  assert (scan_check_delete (scanner, &expected));
  set_token (&expected, t_comp, 14, 3, NULL, 0);
  assert (scan_check_delete (scanner, &expected));
  set_token (&expected, t_bxor, 15, 1, NULL, 0);
  assert (scan_check_delete (scanner, &expected));
  set_token (&expected, t_bor, 15, 3, NULL, 0);
  assert (scan_check_delete (scanner, &expected));
  set_token (&expected, t_band, 15, 5, NULL, 0);
  assert (scan_check_delete (scanner, &expected));
  set_token (&expected, t_int_max, 15, 7, NULL, 0);
  assert (scan_check_delete (scanner, &expected));
  set_token (&expected, t_int_min, 15, 15, NULL, 0);
  assert (scan_check_delete (scanner, &expected));
  set_token (&expected, t_eof, 16, 1, NULL, 0);
  assert (scan_check_delete (scanner, &expected));
  /* clean up */
  delete_scanner (scanner);
  finalise_memory_management ();
  fclose (finput);
}

void
test_scan_all_tokens_unix ()
{
  test_scan_all_tokens ("input/all_tokens_unix.c32sat");
}

void
test_scan_all_tokens_windows ()
{
  test_scan_all_tokens ("input/all_tokens_windows.c32sat");
}

void
test_scan_max_8_bit_constant ()
{
  FILE *input = fopen ("input/scanner_max_8_bit_constant.c32sat", "r");
  Token expected;
  Scanner *scanner = NULL;
  ext_number_of_bits = 8;
  init_memory_management ();
  init_error_management (stderr);
  scanner = create_scanner (input);
  set_token (&expected, t_integer, 1, 1, NULL, MAX_INT_VAL_8);
  assert (scan_check_delete (scanner, &expected));
  set_token (&expected, t_eof, 2, 1, NULL, 0);
  assert (scan_check_delete (scanner, &expected));
  delete_scanner (scanner);
  finalise_memory_management ();
  fclose (input);
  ext_number_of_bits = CONFIG_DEFAULT_NUMBER_OF_BITS;
}

void
test_scan_max_16_bit_constant ()
{
  FILE *input = fopen ("input/scanner_max_16_bit_constant.c32sat", "r");
  Token expected;
  Scanner *scanner = NULL;
  ext_number_of_bits = 16;
  init_memory_management ();
  init_error_management (stderr);
  scanner = create_scanner (input);
  set_token (&expected, t_integer, 1, 1, NULL, MAX_INT_VAL_16);
  assert (scan_check_delete (scanner, &expected));
  set_token (&expected, t_eof, 2, 1, NULL, 0);
  assert (scan_check_delete (scanner, &expected));
  delete_scanner (scanner);
  finalise_memory_management ();
  fclose (input);
  ext_number_of_bits = CONFIG_DEFAULT_NUMBER_OF_BITS;
}

void
test_scan_max_32_bit_constant ()
{
  FILE *input = fopen ("input/scanner_max_32_bit_constant.c32sat", "r");
  Token expected;
  Scanner *scanner = NULL;
  ext_number_of_bits = 32;
  init_memory_management ();
  init_error_management (stderr);
  scanner = create_scanner (input);
  set_token (&expected, t_integer, 1, 1, NULL, MAX_INT_VAL_32);
  assert (scan_check_delete (scanner, &expected));
  set_token (&expected, t_eof, 2, 1, NULL, 0);
  assert (scan_check_delete (scanner, &expected));
  delete_scanner (scanner);
  finalise_memory_management ();
  fclose (input);
  ext_number_of_bits = CONFIG_DEFAULT_NUMBER_OF_BITS;
}

void
test_scan_max_64_bit_constant ()
{
  FILE *input = fopen ("input/scanner_max_64_bit_constant.c32sat", "r");
  Token expected;
  Scanner *scanner = NULL;
  ext_number_of_bits = 64;
  init_memory_management ();
  init_error_management (stderr);
  scanner = create_scanner (input);
  set_token (&expected, t_integer, 1, 1, NULL, 0);
  expected.val = MAX_INT_VAL_64;
  assert (scan_check_delete (scanner, &expected));
  set_token (&expected, t_eof, 2, 1, NULL, 0);
  assert (scan_check_delete (scanner, &expected));
  delete_scanner (scanner);
  finalise_memory_management ();
  fclose (input);
  ext_number_of_bits = CONFIG_DEFAULT_NUMBER_OF_BITS;
}

void
test_scanner_errors ()
{
  /* init */
  FILE *input = fopen ("input/scanner_errors.c32sat", "r");
  FILE *error_output = fopen ("output/scanner_errors_output.txt", "w");
  Token expected;
  Scanner *scanner = NULL;
  init_memory_management ();
  init_error_management (error_output);
  scanner = create_scanner (input);
  /* start test */
  /* invalid character */
  set_token (&expected, t_none, 1, 1, NULL, 0);
  assert (scan_check_delete (scanner, &expected));
  reset_errors ();
  set_token (&expected, t_none, 1, 3, NULL, 0);
  assert (scan_check_delete (scanner, &expected));
  reset_errors ();
  set_token (&expected, t_none, 1, 5, NULL, 0);
  assert (scan_check_delete (scanner, &expected));
  reset_errors ();
  set_token (&expected, t_none, 1, 7, NULL, 0);
  assert (scan_check_delete (scanner, &expected));
  reset_errors ();
  set_token (&expected, t_none, 1, 8, NULL, 0);
  assert (scan_check_delete (scanner, &expected));
  reset_errors ();
  set_token (&expected, t_none, 1, 11, NULL, 0);
  assert (scan_check_delete (scanner, &expected));
  reset_errors ();
  set_token (&expected, t_none, 1, 13, NULL, 0);
  assert (scan_check_delete (scanner, &expected));
  reset_errors ();
  /* too big integer constants */
  set_token (&expected, t_none, 2, 1, NULL, 0);
  assert (scan_check_delete (scanner, &expected));
  reset_errors ();
  set_token (&expected, t_none, 2, 13, NULL, 0);
  assert (scan_check_delete (scanner, &expected));
  reset_errors ();
  set_token (&expected, t_none, 3, 1, NULL, 0);
  assert (scan_check_delete (scanner, &expected));
  reset_errors ();
  set_token (&expected, t_none, 3, 12, NULL, 0);
  assert (scan_check_delete (scanner, &expected));
  reset_errors ();
  /* ident too long */
  set_token (&expected, t_none, 4, 1, NULL, 0);
  assert (scan_check_delete (scanner, &expected));
  reset_errors ();
  set_token (&expected, t_none, 5, 1, NULL, 0);
  assert (scan_check_delete (scanner, &expected));
  reset_errors ();
  /* leading zero */
  set_token (&expected, t_none, 6, 1, NULL, 0);
  assert (scan_check_delete (scanner, &expected));
  reset_errors ();
  set_token (&expected, t_none, 6, 4, NULL, 0);
  assert (scan_check_delete (scanner, &expected));
  reset_errors ();
  set_token (&expected, t_none, 6, 8, NULL, 0);
  assert (scan_check_delete (scanner, &expected));
  reset_errors ();
  set_token (&expected, t_none, 6, 19, NULL, 0);
  assert (scan_check_delete (scanner, &expected));
  reset_errors ();
  set_token (&expected, t_none, 7, 1, NULL, 0);
  assert (scan_check_delete (scanner, &expected));
  reset_errors ();
  set_token (&expected, t_eof, 9, 1, NULL, 0);
  assert (scan_check_delete (scanner, &expected));
  reset_errors ();
  /* clean up */
  delete_scanner (scanner);
  finalise_memory_management ();
  fclose (input);
  fclose (error_output);
}

void
test_special_error (char *input, char *output)
{
  /* init */
  FILE *finput = fopen (input, "r");
  FILE *error_output = fopen (output, "w");
  Token expected;
  Scanner *scanner = NULL;
  init_error_management (error_output);
  init_memory_management ();
  scanner = create_scanner (finput);
  /* start test */
  set_token (&expected, t_none, 1, 1, NULL, 0);
  assert (scan_check_delete (scanner, &expected));
  reset_errors ();
  set_token (&expected, t_none, 2, 1, NULL, 0);
  assert (scan_check_delete (scanner, &expected));
  reset_errors ();
  set_token (&expected, t_eof, 2, 2, NULL, 0);
  assert (scan_check_delete (scanner, &expected));
  reset_errors ();
  /* clean up */
  delete_scanner (scanner);
  finalise_memory_management ();
  fclose (finput);
  fclose (error_output);
}

void
test_special_error_unix ()
{
  test_special_error ("input/scanner_special_error_unix.c32sat",
                      "output/scanner_special_error_unix_output.txt");
}

void
test_special_error_windows ()
{
  test_special_error ("input/scanner_special_error_windows.c32sat",
                      "output/scanner_special_error_windows_output.txt");
}

void
test_scan_formula1 ()
{
  /* init */
  FILE *input = fopen ("input/formula1.c32sat", "r");
  Token expected;
  Scanner *scanner = NULL;
  init_error_management (stderr);
  init_memory_management ();
  scanner = create_scanner (input);
  /* start test */
  set_token (&expected, t_ident, 1, 1, "x", 0);
  assert (scan_check_delete (scanner, &expected));
  set_token (&expected, t_eq, 1, 3, NULL, 0);
  assert (scan_check_delete (scanner, &expected));
  set_token (&expected, t_integer, 1, 6, NULL, 2);
  assert (scan_check_delete (scanner, &expected));
  set_token (&expected, t_and, 1, 8, NULL, 0);
  assert (scan_check_delete (scanner, &expected));
  set_token (&expected, t_ident, 1, 11, "y", 0);
  assert (scan_check_delete (scanner, &expected));
  set_token (&expected, t_eq, 1, 13, NULL, 0);
  assert (scan_check_delete (scanner, &expected));
  set_token (&expected, t_integer, 1, 16, NULL, 3);
  assert (scan_check_delete (scanner, &expected));
  set_token (&expected, t_imp, 1, 18, NULL, 0);
  assert (scan_check_delete (scanner, &expected));
  set_token (&expected, t_ident, 1, 21, "y", 0);
  assert (scan_check_delete (scanner, &expected));
  set_token (&expected, t_eq, 1, 23, NULL, 0);
  assert (scan_check_delete (scanner, &expected));
  set_token (&expected, t_ident, 1, 26, "x", 0);
  assert (scan_check_delete (scanner, &expected));
  set_token (&expected, t_plus, 1, 28, NULL, 0);
  assert (scan_check_delete (scanner, &expected));
  set_token (&expected, t_integer, 1, 30, NULL, 1);
  assert (scan_check_delete (scanner, &expected));
  set_token (&expected, t_eof, 1, 31, NULL, 0);
  assert (scan_check_delete (scanner, &expected));
  /* clean up */
  delete_scanner (scanner);
  finalise_memory_management ();
  fclose (input);
}

void
test_scan_formula2 ()
{
  /* init */
  FILE *input = fopen ("input/formula2.c32sat", "r");
  Token expected;
  Scanner *scanner = NULL;
  init_error_management (stderr);
  init_memory_management ();
  scanner = create_scanner (input);
  /* start test */
  set_token (&expected, t_ident, 1, 1, "x", 0);
  assert (scan_check_delete (scanner, &expected));
  set_token (&expected, t_gt, 1, 3, NULL, 0);
  assert (scan_check_delete (scanner, &expected));
  set_token (&expected, t_ident, 1, 5, "y", 0);
  assert (scan_check_delete (scanner, &expected));
  set_token (&expected, t_and, 1, 7, NULL, 0);
  assert (scan_check_delete (scanner, &expected));
  set_token (&expected, t_ident, 1, 10, "y", 0);
  assert (scan_check_delete (scanner, &expected));
  set_token (&expected, t_gt, 1, 12, NULL, 0);
  assert (scan_check_delete (scanner, &expected));
  set_token (&expected, t_ident, 1, 14, "z", 0);
  assert (scan_check_delete (scanner, &expected));
  set_token (&expected, t_imp, 1, 16, NULL, 0);
  assert (scan_check_delete (scanner, &expected));
  set_token (&expected, t_ident, 1, 19, "x", 0);
  assert (scan_check_delete (scanner, &expected));
  set_token (&expected, t_gt, 1, 21, NULL, 0);
  assert (scan_check_delete (scanner, &expected));
  set_token (&expected, t_ident, 1, 23, "z", 0);
  assert (scan_check_delete (scanner, &expected));
  set_token (&expected, t_eof, 1, 24, NULL, 0);
  assert (scan_check_delete (scanner, &expected));
  /* clean up */
  delete_scanner (scanner);
  finalise_memory_management ();
  fclose (input);
}

void
test_scan_formula3 ()
{
  /* init */
  FILE *input = fopen ("input/formula3.c32sat", "r");
  Token expected;
  Scanner *scanner = NULL;
  init_error_management (stderr);
  init_memory_management ();
  scanner = create_scanner (input);
  /* start test */
  set_token (&expected, t_lpar, 1, 1, NULL, 0);
  assert (scan_check_delete (scanner, &expected));
  set_token (&expected, t_lpar, 1, 2, NULL, 0);
  assert (scan_check_delete (scanner, &expected));
  set_token (&expected, t_lpar, 1, 3, NULL, 0);
  assert (scan_check_delete (scanner, &expected));
  set_token (&expected, t_minus, 1, 4, NULL, 0);
  assert (scan_check_delete (scanner, &expected));
  set_token (&expected, t_integer, 1, 5, NULL, 4);
  assert (scan_check_delete (scanner, &expected));
  set_token (&expected, t_rpar, 1, 6, NULL, 0);
  assert (scan_check_delete (scanner, &expected));
  set_token (&expected, t_div, 1, 7, NULL, 0);
  assert (scan_check_delete (scanner, &expected));
  set_token (&expected, t_integer, 1, 8, NULL, 2);
  assert (scan_check_delete (scanner, &expected));
  set_token (&expected, t_rpar, 1, 9, NULL, 0);
  assert (scan_check_delete (scanner, &expected));
  set_token (&expected, t_plus, 1, 10, NULL, 0);
  assert (scan_check_delete (scanner, &expected));
  set_token (&expected, t_integer, 1, 11, NULL, 3);
  assert (scan_check_delete (scanner, &expected));
  set_token (&expected, t_rpar, 1, 12, NULL, 0);
  assert (scan_check_delete (scanner, &expected));
  set_token (&expected, t_mult, 1, 13, NULL, 0);
  assert (scan_check_delete (scanner, &expected));
  set_token (&expected, t_lpar, 1, 14, NULL, 0);
  assert (scan_check_delete (scanner, &expected));
  set_token (&expected, t_lpar, 1, 15, NULL, 0);
  assert (scan_check_delete (scanner, &expected));
  set_token (&expected, t_integer, 1, 16, NULL, 9);
  assert (scan_check_delete (scanner, &expected));
  set_token (&expected, t_minus, 1, 17, NULL, 0);
  assert (scan_check_delete (scanner, &expected));
  set_token (&expected, t_integer, 1, 18, NULL, 3);
  assert (scan_check_delete (scanner, &expected));
  set_token (&expected, t_rpar, 1, 19, NULL, 0);
  assert (scan_check_delete (scanner, &expected));
  set_token (&expected, t_div, 1, 20, NULL, 0);
  assert (scan_check_delete (scanner, &expected));
  set_token (&expected, t_integer, 1, 21, NULL, 2);
  assert (scan_check_delete (scanner, &expected));
  set_token (&expected, t_rpar, 1, 22, NULL, 0);
  assert (scan_check_delete (scanner, &expected));
  set_token (&expected, t_eq, 1, 23, NULL, 0);
  assert (scan_check_delete (scanner, &expected));
  set_token (&expected, t_integer, 1, 25, NULL, 3);
  assert (scan_check_delete (scanner, &expected));
  set_token (&expected, t_eof, 1, 26, NULL, 0);
  assert (scan_check_delete (scanner, &expected));
  /* clean up */
  delete_scanner (scanner);
  finalise_memory_management ();
  fclose (input);
}

void
test_scan_formula4 ()
{
  /* init */
  FILE *input = fopen ("input/formula4.c32sat", "r");
  Token expected;
  Scanner *scanner = NULL;
  init_error_management (stderr);
  init_memory_management ();
  scanner = create_scanner (input);
  /* start test */
  set_token (&expected, t_lpar, 1, 1, NULL, 0);
  assert (scan_check_delete (scanner, &expected));
  set_token (&expected, t_lpar, 1, 2, NULL, 0);
  assert (scan_check_delete (scanner, &expected));
  set_token (&expected, t_ident, 1, 3, "x", 0);
  assert (scan_check_delete (scanner, &expected));
  set_token (&expected, t_eq, 1, 5, NULL, 0);
  assert (scan_check_delete (scanner, &expected));
  set_token (&expected, t_integer, 1, 8, NULL, 0);
  assert (scan_check_delete (scanner, &expected));
  set_token (&expected, t_and, 1, 10, NULL, 0);
  assert (scan_check_delete (scanner, &expected));
  set_token (&expected, t_ident, 1, 13, "y", 0);
  assert (scan_check_delete (scanner, &expected));
  set_token (&expected, t_eq, 1, 15, NULL, 0);
  assert (scan_check_delete (scanner, &expected));
  set_token (&expected, t_integer, 1, 18, NULL, 1);
  assert (scan_check_delete (scanner, &expected));
  set_token (&expected, t_rpar, 1, 19, NULL, 0);
  assert (scan_check_delete (scanner, &expected));
  set_token (&expected, t_and, 1, 21, NULL, 0);
  assert (scan_check_delete (scanner, &expected));
  set_token (&expected, t_not, 1, 24, NULL, 0);
  assert (scan_check_delete (scanner, &expected));
  set_token (&expected, t_lpar, 1, 25, NULL, 0);
  assert (scan_check_delete (scanner, &expected));
  set_token (&expected, t_not, 1, 26, NULL, 0);
  assert (scan_check_delete (scanner, &expected));
  set_token (&expected, t_ident, 1, 27, "x", 0);
  assert (scan_check_delete (scanner, &expected));
  set_token (&expected, t_band, 1, 29, NULL, 0);
  assert (scan_check_delete (scanner, &expected));
  set_token (&expected, t_ident, 1, 31, "x", 0);
  assert (scan_check_delete (scanner, &expected));
  set_token (&expected, t_or, 1, 33, NULL, 0);
  assert (scan_check_delete (scanner, &expected));
  set_token (&expected, t_ident, 1, 36, "y", 0);
  assert (scan_check_delete (scanner, &expected));
  set_token (&expected, t_bor, 1, 38, NULL, 0);
  assert (scan_check_delete (scanner, &expected));
  set_token (&expected, t_not, 1, 40, NULL, 0);
  assert (scan_check_delete (scanner, &expected));
  set_token (&expected, t_lpar, 1, 41, NULL, 0);
  assert (scan_check_delete (scanner, &expected));
  set_token (&expected, t_ident, 1, 42, "y", 0);
  assert (scan_check_delete (scanner, &expected));
  set_token (&expected, t_bxor, 1, 44, NULL, 0);
  assert (scan_check_delete (scanner, &expected));
  set_token (&expected, t_ident, 1, 46, "x", 0);
  assert (scan_check_delete (scanner, &expected));
  set_token (&expected, t_rpar, 1, 47, NULL, 0);
  assert (scan_check_delete (scanner, &expected));
  set_token (&expected, t_rpar, 1, 48, NULL, 0);
  assert (scan_check_delete (scanner, &expected));
  set_token (&expected, t_dimp, 2, 1, NULL, 0);
  assert (scan_check_delete (scanner, &expected));
  set_token (&expected, t_lpar, 3, 1, NULL, 0);
  assert (scan_check_delete (scanner, &expected));
  set_token (&expected, t_comp, 3, 2, NULL, 0);
  assert (scan_check_delete (scanner, &expected));
  set_token (&expected, t_ident, 3, 3, "y", 0);
  assert (scan_check_delete (scanner, &expected));
  set_token (&expected, t_rpar, 3, 4, NULL, 0);
  assert (scan_check_delete (scanner, &expected));
  set_token (&expected, t_mult, 3, 6, NULL, 0);
  assert (scan_check_delete (scanner, &expected));
  set_token (&expected, t_lpar, 3, 8, NULL, 0);
  assert (scan_check_delete (scanner, &expected));
  set_token (&expected, t_ident, 3, 9, "x", 0);
  assert (scan_check_delete (scanner, &expected));
  set_token (&expected, t_shiftr, 3, 11, NULL, 0);
  assert (scan_check_delete (scanner, &expected));
  set_token (&expected, t_integer, 3, 14, NULL, 2);
  assert (scan_check_delete (scanner, &expected));
  set_token (&expected, t_div, 3, 16, NULL, 0);
  assert (scan_check_delete (scanner, &expected));
  set_token (&expected, t_lpar, 3, 18, NULL, 0);
  assert (scan_check_delete (scanner, &expected));
  set_token (&expected, t_ident, 3, 19, "y", 0);
  assert (scan_check_delete (scanner, &expected));
  set_token (&expected, t_shiftl, 3, 21, NULL, 0);
  assert (scan_check_delete (scanner, &expected));
  set_token (&expected, t_integer, 3, 24, NULL, 3);
  assert (scan_check_delete (scanner, &expected));
  set_token (&expected, t_rpar, 3, 25, NULL, 0);
  assert (scan_check_delete (scanner, &expected));
  set_token (&expected, t_rpar, 3, 26, NULL, 0);
  assert (scan_check_delete (scanner, &expected));
  set_token (&expected, t_gte, 3, 28, NULL, 0);
  assert (scan_check_delete (scanner, &expected));
  set_token (&expected, t_integer, 3, 31, NULL, 3);
  assert (scan_check_delete (scanner, &expected));
  set_token (&expected, t_mod, 3, 33, NULL, 0);
  assert (scan_check_delete (scanner, &expected));
  set_token (&expected, t_lpar, 3, 35, NULL, 0);
  assert (scan_check_delete (scanner, &expected));
  set_token (&expected, t_ident, 3, 36, "x", 0);
  assert (scan_check_delete (scanner, &expected));
  set_token (&expected, t_gt, 3, 38, NULL, 0);
  assert (scan_check_delete (scanner, &expected));
  set_token (&expected, t_integer, 3, 40, NULL, 3);
  assert (scan_check_delete (scanner, &expected));
  set_token (&expected, t_qm, 3, 42, NULL, 0);
  assert (scan_check_delete (scanner, &expected));
  set_token (&expected, t_integer, 3, 44, NULL, 7);
  assert (scan_check_delete (scanner, &expected));
  set_token (&expected, t_colon, 3, 45, NULL, 0);
  assert (scan_check_delete (scanner, &expected));
  set_token (&expected, t_integer, 3, 46, NULL, 8);
  assert (scan_check_delete (scanner, &expected));
  set_token (&expected, t_rpar, 3, 47, NULL, 0);
  assert (scan_check_delete (scanner, &expected));
  set_token (&expected, t_rpar, 3, 48, NULL, 0);
  assert (scan_check_delete (scanner, &expected));
  set_token (&expected, t_eof, 3, 49, NULL, 0);
  assert (scan_check_delete (scanner, &expected));
  /* clean up */
  delete_scanner (scanner);
  finalise_memory_management ();
  fclose (input);
}

void
run_scanner_tests ()
{
  run_test (test_create_delete_scanner);
  run_test (test_scan_all_tokens_unix);
  run_test (test_scan_all_tokens_windows);
  run_test (test_scan_max_8_bit_constant);
  run_test (test_scan_max_16_bit_constant);
  run_test (test_scan_max_32_bit_constant);
  run_test (test_scan_max_64_bit_constant);
  run_test (test_scanner_errors);
  check_output ("output/scanner_errors_expected.txt",
                "output/scanner_errors_output.txt");
  run_test (test_special_error_unix);
  check_output ("output/scanner_special_error_unix_expected.txt",
                "output/scanner_special_error_unix_output.txt");
  run_test (test_special_error_windows);
  check_output ("output/scanner_special_error_windows_expected.txt",
                "output/scanner_special_error_windows_output.txt");
  run_test (test_scan_formula1);
  run_test (test_scan_formula2);
  run_test (test_scan_formula3);
  run_test (test_scan_formula4);

}
