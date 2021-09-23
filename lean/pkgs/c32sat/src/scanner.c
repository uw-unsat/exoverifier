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
#include <stdlib.h>
#include <assert.h>
#include <ctype.h>
#include <string.h>
#include "token.h"
#include "error_management.h"
#include "scanner.h"
#include "bool.h"
#include "memory_management.h"
#include "c32sat_math.h"
#include "config.h"

static const char *int_max_str = "INT_MAX";
static const char *int_min_str = "INT_MIN";

enum CommentState
{
  cs_comment = 0,
  cs_asterisk,
  cs_end_of_comment
};

typedef enum CommentState CommentState;

static long long int
string_to_long_long (char *str, int length)
{
  long long int result = 0;
  int i = 0;
  assert (length > 0);
  for (i = 0; i < length; i++)
    {
      result += (str[i] - 48) * pow10_ull_c32sat_math (length - i - 1);
    }
  return result;
}

static unsigned long long int
string_to_unsigned_long_long (char *str, int length)
{
  unsigned long long int result = 0;
  int i = 0;
  assert (length > 0);
  for (i = 0; i < length; i++)
    {
      result += (str[i] - 48) * pow10_ull_c32sat_math (length - i - 1);
    }
  return result;
}

static void
next_char (Scanner * scanner)
{
  if (scanner->cur != EOF)
    {
      scanner->cur = fgetc (scanner->input);
      scanner->col++;
      if (scanner->cur == 10)
        {                       /* LF */
          scanner->line++;
          scanner->col = 0;
        }
      else if (scanner->cur == 13)
        {                       /* CR */
          next_char (scanner);
        }
    }
}

Scanner *
create_scanner (FILE * input)
{
  Scanner *scanner = NULL;
  assert (input != NULL
          && (ext_number_of_bits == 4 
              || ext_number_of_bits == 8 || ext_number_of_bits == 16
              || ext_number_of_bits == 32 || ext_number_of_bits == 64));
  scanner = (Scanner *) malloc_c32sat (sizeof (Scanner));
  scanner->input = input;
  scanner->cur = 0;
  scanner->line = 1;
  scanner->col = 0;
  if (ext_number_of_bits == 64)
    {
      scanner->max_int_val = MAX_INT_VAL_64;
      scanner->max_int_string_length = MAX_INT_STRING_LENGTH_64;
    }
  else if (ext_number_of_bits == 32)
    {
      scanner->max_int_val = MAX_INT_VAL_32;
      scanner->max_int_string_length = MAX_INT_STRING_LENGTH_32;
    }
  else if (ext_number_of_bits == 16)
    {
      scanner->max_int_val = MAX_INT_VAL_16;
      scanner->max_int_string_length = MAX_INT_STRING_LENGTH_16;
    }
  else if (ext_number_of_bits == 8)
    {
      scanner->max_int_val = MAX_INT_VAL_8;
      scanner->max_int_string_length = MAX_INT_STRING_LENGTH_8;
    }
  else
    {
      assert (ext_number_of_bits == 4);
      scanner->max_int_val = MAX_INT_VAL_4;
      scanner->max_int_string_length = MAX_INT_STRING_LENGTH_4;
    }   
  next_char (scanner);
  return scanner;
}

void
delete_scanner (Scanner * scanner)
{
  assert (scanner != NULL);
  free_c32sat (scanner, sizeof (Scanner));
}

static Token *
read_ident_and_keywords (Scanner * scanner, unsigned int line, unsigned int col)
{
  int counter = 0;
  Token *result = NULL;
  char buffer[MAX_IDENT_LENGTH + 1];
  unsigned int pos = 0;
  while (isalnum (scanner->cur) || scanner->cur == '_')
    {
      if (counter < MAX_IDENT_LENGTH)
        {
          buffer[pos++] = scanner->cur;
        }
      next_char (scanner);
      counter++;
    }
  buffer[pos] = '\0';
  if (counter > MAX_IDENT_LENGTH)
    {
      error (e_scanner_ident_too_long, line, col, 0, buffer);
      result = create_token (t_none, line, col);
      return result;
    }
  if (strcmp (buffer, int_max_str) == 0){
    result = create_token(t_int_max, line, col);
  } else if(strcmp (buffer, int_min_str) == 0){
    result = create_token(t_int_min, line, col);
  } else {
    result = create_ident_token (buffer, line, col);
  }
  assert (result != NULL);
  return result;
}

static Token *
read_integer (Scanner * scanner, unsigned int line, unsigned int col)
{ 
  Bool zero_first = b_false;
  int counter = 0;
  long long int val = 0;
  char buffer[scanner->max_int_string_length + 1];
  Token *result = NULL;
  unsigned int pos = 0;
  if (scanner->cur == '0'){
    zero_first = b_true;
  }
  while (isdigit (scanner->cur))
    {
      if (counter < scanner->max_int_string_length)
        {
          buffer[pos++] = scanner->cur;
        }
      next_char (scanner);
      counter++;
    }
  buffer[pos] = '\0';
  if (zero_first && (counter > 1))
    {
      error (e_scanner_lead_zero, line, col, counter, buffer);
      return create_token (t_none, line, col);
    }
  if (counter > scanner->max_int_string_length)
    {

      error (e_scanner_int_too_big, line, col, b_false, buffer);
      result = create_token (t_none, line, col);
    }
  else if ((counter == scanner->max_int_string_length)
           &&
           (string_to_unsigned_long_long
            (buffer,
             scanner->max_int_string_length) >
            (unsigned long long int) scanner->max_int_val))
    {

      error (e_scanner_int_too_big, line, col, b_true, buffer);
      result = create_token (t_none, line, col);
    }
  else
    {
      val = string_to_long_long (buffer, counter);
      result = create_integer_token (val, line, col);
    }
  assert (result != NULL);
  return result;
}

static void
skip_comment (Scanner * scanner)
{
  CommentState state = cs_comment;
  while (scanner->cur != EOF && state != cs_end_of_comment)
    {
      switch (state)
        {
        case cs_comment:
          if (scanner->cur == '*')
            {
              state = cs_asterisk;
            }
          break;
        default:               /* cs_asterisk */
          if (scanner->cur == '/')
            {
              state = cs_end_of_comment;
            }
          else if (scanner->cur != '*')
            {
              state = cs_comment;
            }
          break;
        }
      next_char (scanner);
    }
}

Token *
scan (Scanner * scanner)
{
  unsigned int line = 0;
  unsigned int col = 0;
  Token *result = NULL;
  assert (scanner != NULL);
  assert (scanner->input != NULL);
  while (isspace (scanner->cur))
    {                           /* Skip whitespaces */
      next_char (scanner);
    }
  line = scanner->line;
  col = scanner->col;
  if (isalpha (scanner->cur) || scanner->cur == '_')
    {
      result = read_ident_and_keywords (scanner, line, col);
    }
  else if (isdigit (scanner->cur))
    {
      result = read_integer (scanner, line, col);
    }
  else
    {
      switch (scanner->cur)
        {
        case '=':
          next_char (scanner);
          switch (scanner->cur)
            {
            case '>':
              result = create_token (t_imp, line, col);
              next_char (scanner);
              break;
            case '=':
              result = create_token (t_eq, line, col);
              next_char (scanner);
              break;
            default:
              error (e_scanner_invalid_equal, line, col + 1,
                     scanner->cur, NULL);
              result = create_token (t_none, line, col);
              break;
            }
          break;
        case '<':
          next_char (scanner);
          switch (scanner->cur)
            {
            case '=':
              next_char (scanner);
              if (scanner->cur == '>')
                {
                  result = create_token (t_dimp, line, col);
                  next_char (scanner);
                }
              else
                {
                  result = create_token (t_lte, line, col);
                }
              break;
            case '<':
              result = create_token (t_shiftl, line, col);
              next_char (scanner);
              break;
            default:           /* t_lt */
              result = create_token (t_lt, line, col);
              break;
            }
          break;
        case '>':
          next_char (scanner);
          switch (scanner->cur)
            {
            case '=':
              result = create_token (t_gte, line, col);
              next_char (scanner);
              break;
            case '>':
              result = create_token (t_shiftr, line, col);
              next_char (scanner);
              break;
            default:           /* t_gt */
              result = create_token (t_gt, line, col);
              break;
            }
          break;
        case '!':
          next_char (scanner);
          if (scanner->cur == '=')
            {
              result = create_token (t_neq, line, col);
              next_char (scanner);
              break;
            }
          else
            {
              result = create_token (t_not, line, col);
            }
          break;
        case '|':
          next_char (scanner);
          if (scanner->cur == '|')
            {
              result = create_token (t_or, line, col);
              next_char (scanner);
            }
          else
            {
              result = create_token (t_bor, line, col);
            }
          break;
        case '&':
          next_char (scanner);
          if (scanner->cur == '&')
            {
              result = create_token (t_and, line, col);
              next_char (scanner);
            }
          else
            {
              result = create_token (t_band, line, col);
            }
          break;
        case '(':
          result = create_token (t_lpar, line, col);
          next_char (scanner);
          break;
        case ')':
          result = create_token (t_rpar, line, col);
          next_char (scanner);
          break;
        case '+':
          result = create_token (t_plus, line, col);
          next_char (scanner);
          break;
        case '-':
          result = create_token (t_minus, line, col);
          next_char (scanner);
          break;
        case '*':
          result = create_token (t_mult, line, col);
          next_char (scanner);
          break;
        case '/':
          next_char (scanner);
          if (scanner->cur == '*')
            {
              next_char (scanner);
              skip_comment (scanner);
              result = scan (scanner);
            }
          else
            {
              result = create_token (t_div, line, col);
            }
          break;
        case '%':
          result = create_token (t_mod, line, col);
          next_char (scanner);
          break;
        case '~':
          result = create_token (t_comp, line, col);
          next_char (scanner);
          break;
        case '?':
          result = create_token (t_qm, line, col);
          next_char (scanner);
          break;
        case ':':
          result = create_token (t_colon, line, col);
          next_char (scanner);
          break;
        case '^':
          result = create_token (t_bxor, line, col);
          next_char (scanner);
          break;
        case EOF:
          result = create_token (t_eof, line, col);
          break;
        default:
          error (e_scanner_invalid_char, line, col, scanner->cur, NULL);
          result = create_token (t_none, line, col);
          next_char (scanner);
          break;
        }
    }
  assert (result != NULL);
  return result;
}
