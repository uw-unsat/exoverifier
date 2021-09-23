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
#include "symbol.h"
#include "token.h"
#include "parse_tree.h"

static const char *symbols[] =
  { "(", ")", ":", "?", "=>", "<=>", "||", "&&", "|", "^",
  "&", "==", "!=", "<", "<=", ">", ">=", ">>",
  "<<", "+", "-", "*", "/", "%", "!", "~", "EOF"
};

const char *
get_symbol (SymbolKind kind)
{
  return symbols[kind];
}

const char *
get_token_symbol (TokenKind kind)
{
  const char *result = NULL;
  assert (kind != t_none && kind != t_ident && kind != t_integer);
  switch (kind)
    {
    case t_lpar:
      result = symbols[s_lpar];
      break;
    case t_rpar:
      result = symbols[s_rpar];
      break;
    case t_colon:
      result = symbols[s_colon];
      break;
    case t_qm:
      result = symbols[s_qm];
      break;
    case t_imp:
      result = symbols[s_imp];
      break;
    case t_dimp:
      result = symbols[s_dimp];
      break;
    case t_or:
      result = symbols[s_or];
      break;
    case t_and:
      result = symbols[s_and];
      break;
    case t_bor:
      result = symbols[s_bor];
      break;
    case t_bxor:
      result = symbols[s_bxor];
      break;
    case t_band:
      result = symbols[s_band];
      break;
    case t_eq:
      result = symbols[s_eq];
      break;
    case t_neq:
      result = symbols[s_neq];
      break;
    case t_lt:
      result = symbols[s_lt];
      break;
    case t_lte:
      result = symbols[s_lte];
      break;
    case t_gt:
      result = symbols[s_gt];
      break;
    case t_gte:
      result = symbols[s_gte];
      break;
    case t_shiftr:
      result = symbols[s_shiftr];
      break;
    case t_shiftl:
      result = symbols[s_shiftl];
      break;
    case t_plus:
      result = symbols[s_plus];
      break;
    case t_minus:
      result = symbols[s_minus];
      break;
    case t_mult:
      result = symbols[s_mult];
      break;
    case t_div:
      result = symbols[s_div];
      break;
    case t_mod:
      result = symbols[s_mod];
      break;
    case t_not:
      result = symbols[s_not];
      break;
    case t_comp:
      result = symbols[s_comp];
      break;
    case t_eof:
      result = symbols[s_eof];
      break;
    default:
      assert (0);
    }
  assert (result != NULL);
  return result;
}

const char *
get_parse_tree_node_symbol (ParseTreeNodeKind kind)
{
  const char *result = NULL;
  assert (kind != ptn_ident && kind != ptn_integer);
  switch (kind)
    {
    case ptn_qm:
      result = symbols[s_qm];
      break;
    case ptn_imp:
      result = symbols[s_imp];
      break;
    case ptn_dimp:
      result = symbols[s_dimp];
      break;
    case ptn_or:
      result = symbols[s_or];
      break;
    case ptn_and:
      result = symbols[s_and];
      break;
    case ptn_bor:
      result = symbols[s_bor];
      break;
    case ptn_bxor:
      result = symbols[s_bxor];
      break;
    case ptn_band:
      result = symbols[s_band];
      break;
    case ptn_eq:
      result = symbols[s_eq];
      break;
    case ptn_neq:
      result = symbols[s_neq];
      break;
    case ptn_lt:
      result = symbols[s_lt];
      break;
    case ptn_lte:
      result = symbols[s_lte];
      break;
    case ptn_gt:
      result = symbols[s_gt];
      break;
    case ptn_gte:
      result = symbols[s_gte];
      break;
    case ptn_shiftr:
      result = symbols[s_shiftr];
      break;
    case ptn_shiftl:
      result = symbols[s_shiftl];
      break;
    case ptn_plus:
      result = symbols[s_plus];
      break;
    case ptn_binary_minus:
    case ptn_unary_minus:
      result = symbols[s_minus];
      break;
    case ptn_mult:
      result = symbols[s_mult];
      break;
    case ptn_div:
      result = symbols[s_div];
      break;
    case ptn_mod:
      result = symbols[s_mod];
      break;
    case ptn_not:
      result = symbols[s_not];
      break;
    case ptn_comp:
      result = symbols[s_comp];
      break;
    default:
      assert (0);
      break;
    }
  assert (result != NULL);
  return result;
}
