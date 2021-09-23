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
#ifndef _SYMBOL_H_
#define _SYMBOL_H_

#include "token.h"
#include "parse_tree.h"

/** The kind of a symbol. */
enum SymbolKind
{
  /** Left parenthis */
  s_lpar = 0,
  /** Right parenthis */
  s_rpar,
  /** Colon */
  s_colon,
  /** Question mark */
  s_qm,
  /** Implication */
  s_imp,
  /** Double implication */
  s_dimp,
  /** Boolean or */
  s_or,
  /** Boolean and */
  s_and,
  /** Bitwise or */
  s_bor,
  /** Bitwise xor */
  s_bxor,
  /** Bitwise and */
  s_band,
  /** Equal */
  s_eq,
  /** Not equal */
  s_neq,
  /** Less than */
  s_lt,
  /** Less than or equal */
  s_lte,
  /** Greater than */
  s_gt,
  /** Greater than or equal */
  s_gte,
  /** Shift right */
  s_shiftr,
  /** Shift left */
  s_shiftl,
  /** Plus */
  s_plus,
  /** Minus */
  s_minus,
  /** Multiplication */
  s_mult,
  /** Integer Divison */
  s_div,
  /** Modulo */
  s_mod,
  /** Boolean not */
  s_not,
  /** Complement */
  s_comp,
  /** End of file */
  s_eof
};

typedef enum SymbolKind SymbolKind;

/** 
 * Returns the string representation of a symbol.
 * @param kind The kind of symbol
 * @return The resulting string representation
 */
const char *get_symbol (SymbolKind kind);

/** 
 * Returns the string representation of a kind of token.
 * @param kind The kind of token
 * @return The resulting string representation
 */
const char *get_token_symbol (TokenKind kind);

/** 
 * Returns the string representation of a kind of parse 
 * tree node.
 * @param kind The kind of parse tree node
 * @return The resulting string representation
 */
const char *get_parse_tree_node_symbol (ParseTreeNodeKind kind);

#endif
