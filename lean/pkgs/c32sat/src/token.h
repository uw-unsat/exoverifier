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
#ifndef _TOKEN_H_
#define _TOKEN_H_

#include "bool.h"

/**
 * Represents all possible token kinds.
 */
enum TokenKind
{
  /** Invalid token */
  t_none = 0,
  /** Identifier */
  t_ident,
  /** Integer */
  t_integer,
  /** Left parenthis */
  t_lpar,
  /** Right parenthis */
  t_rpar,
  /** Colon */
  t_colon,
  /** Question mark */
  t_qm,
  /** Implication */
  t_imp,
  /** Double implication */
  t_dimp,
  /** Boolean or */
  t_or,
  /** Boolean and */
  t_and,
  /** Bitwise or */
  t_bor,
  /** Bitwise xor */
  t_bxor,
  /** Bitwise and */
  t_band,
  /** Equal */
  t_eq,
  /** Not equal */
  t_neq,
  /** Less than */
  t_lt,
  /** Less than or equal */
  t_lte,
  /** Greater than */
  t_gt,
  /** Greater than or equal */
  t_gte,
  /** Shift right */
  t_shiftr,
  /** Shift left */
  t_shiftl,
  /** Plus */
  t_plus,
  /** Minus */
  t_minus,
  /** Multiplication */
  t_mult,
  /** Integer Divison */
  t_div,
  /** Modulo */
  t_mod,
  /** Boolean not */
  t_not,
  /** Complement */
  t_comp,
  /* INT_MIN */
  t_int_min,
  /* INT_MAX */
  t_int_max,
  /** End of file */
  t_eof
};

typedef enum TokenKind TokenKind;

/**
 * @brief Represents a token which is used as input for the
 * parser.
 */
struct Token
{
  /** The line in which the token occurs */
  unsigned int line;
  /** The column where the token begins */
  unsigned int col;
  /** The kind of token */
  TokenKind kind;
  /** The string of the identifier. Used only if the token
   * is an identifier. */
  char *str;
  /** The integer value. Used only if the token is an 
   * integer. */
  long long int val;
};

typedef struct Token Token;

/** Creates a token and returns it.
 * @param kind The kind of token
 * @param line The line in which the token occurs
 * @param col The column where the token begins
 * @return The resulting token
 */
Token *create_token (TokenKind kind, unsigned int line, unsigned int col);

/** Creates a token which represents an identifier and 
 * returns it. The string will be copied.
 * @param str The string representing the identifier
 * @param line The line in which the token occurs
 * @param col The column where the token begins
 * @return The resulting token
 */
Token *create_ident_token (const char *str, unsigned int line,
                           unsigned int col);

/** Creates a token which represents an integer and returns it.
 * @param val The value of the integer
 * @param line The line in which the token occurs
 * @param col The column where the token begins
 * @return The resulting token
 */
Token *create_integer_token (long long int val, unsigned int line,
                             unsigned int col);

/** Deletes a token from memory. If the token represents an
 * identifier then the memory which was allocated for copying
 * the string of the identifier will be freed as well.
 * @param token The token which has to be deleted
 */
void delete_token (Token * token);

#endif
