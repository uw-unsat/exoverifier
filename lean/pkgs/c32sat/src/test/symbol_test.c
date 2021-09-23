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
#include <string.h>
#include "symbol_test.h"
#include "test_logging.h"
#include "../symbol.h"

void
test_get_symbol ()
{
  assert (strcmp (get_symbol (s_lpar), "(") == 0);
  assert (strcmp (get_symbol (s_rpar), ")") == 0);
  assert (strcmp (get_symbol (s_colon), ":") == 0);
  assert (strcmp (get_symbol (s_qm), "?") == 0);
  assert (strcmp (get_symbol (s_imp), "=>") == 0);
  assert (strcmp (get_symbol (s_dimp), "<=>") == 0);
  assert (strcmp (get_symbol (s_or), "||") == 0);
  assert (strcmp (get_symbol (s_and), "&&") == 0);
  assert (strcmp (get_symbol (s_bor), "|") == 0);
  assert (strcmp (get_symbol (s_bxor), "^") == 0);
  assert (strcmp (get_symbol (s_band), "&") == 0);
  assert (strcmp (get_symbol (s_eq), "==") == 0);
  assert (strcmp (get_symbol (s_neq), "!=") == 0);
  assert (strcmp (get_symbol (s_lt), "<") == 0);
  assert (strcmp (get_symbol (s_lte), "<=") == 0);
  assert (strcmp (get_symbol (s_gt), ">") == 0);
  assert (strcmp (get_symbol (s_gte), ">=") == 0);
  assert (strcmp (get_symbol (s_shiftr), ">>") == 0);
  assert (strcmp (get_symbol (s_shiftl), "<<") == 0);
  assert (strcmp (get_symbol (s_plus), "+") == 0);
  assert (strcmp (get_symbol (s_minus), "-") == 0);
  assert (strcmp (get_symbol (s_mult), "*") == 0);
  assert (strcmp (get_symbol (s_div), "/") == 0);
  assert (strcmp (get_symbol (s_mod), "%") == 0);
  assert (strcmp (get_symbol (s_not), "!") == 0);
  assert (strcmp (get_symbol (s_comp), "~") == 0);
  assert (strcmp (get_symbol (s_eof), "EOF") == 0);
}

void
test_get_token_symbol ()
{
  assert (strcmp (get_token_symbol (t_lpar), get_symbol (s_lpar)) == 0);
  assert (strcmp (get_token_symbol (t_rpar), get_symbol (s_rpar)) == 0);
  assert (strcmp (get_token_symbol (t_colon), get_symbol (s_colon)) == 0);
  assert (strcmp (get_token_symbol (t_qm), get_symbol (s_qm)) == 0);
  assert (strcmp (get_token_symbol (t_imp), get_symbol (s_imp)) == 0);
  assert (strcmp (get_token_symbol (t_dimp), get_symbol (s_dimp)) == 0);
  assert (strcmp (get_token_symbol (t_or), get_symbol (s_or)) == 0);
  assert (strcmp (get_token_symbol (t_and), get_symbol (s_and)) == 0);
  assert (strcmp (get_token_symbol (t_bor), get_symbol (s_bor)) == 0);
  assert (strcmp (get_token_symbol (t_bxor), get_symbol (s_bxor)) == 0);
  assert (strcmp (get_token_symbol (t_band), get_symbol (s_band)) == 0);
  assert (strcmp (get_token_symbol (t_eq), get_symbol (s_eq)) == 0);
  assert (strcmp (get_token_symbol (t_neq), get_symbol (s_neq)) == 0);
  assert (strcmp (get_token_symbol (t_lt), get_symbol (s_lt)) == 0);
  assert (strcmp (get_token_symbol (t_lte), get_symbol (s_lte)) == 0);
  assert (strcmp (get_token_symbol (t_gt), get_symbol (s_gt)) == 0);
  assert (strcmp (get_token_symbol (t_gte), get_symbol (s_gte)) == 0);
  assert (strcmp (get_token_symbol (t_shiftr), get_symbol (s_shiftr)) == 0);
  assert (strcmp (get_token_symbol (t_shiftl), get_symbol (s_shiftl)) == 0);
  assert (strcmp (get_token_symbol (t_plus), get_symbol (s_plus)) == 0);
  assert (strcmp (get_token_symbol (t_minus), get_symbol (s_minus)) == 0);
  assert (strcmp (get_token_symbol (t_mult), get_symbol (s_mult)) == 0);
  assert (strcmp (get_token_symbol (t_div), get_symbol (s_div)) == 0);
  assert (strcmp (get_token_symbol (t_mod), get_symbol (s_mod)) == 0);
  assert (strcmp (get_token_symbol (t_not), get_symbol (s_not)) == 0);
  assert (strcmp (get_token_symbol (t_comp), get_symbol (s_comp)) == 0);
  assert (strcmp (get_token_symbol (t_eof), get_symbol (s_eof)) == 0);
}

void
test_get_parse_tree_node_symbol ()
{
  assert (strcmp (get_parse_tree_node_symbol (ptn_qm), get_symbol (s_qm)) ==
          0);
  assert (strcmp (get_parse_tree_node_symbol (ptn_imp), get_symbol (s_imp)) ==
          0);
  assert (strcmp (get_parse_tree_node_symbol (ptn_dimp), get_symbol (s_dimp))
          == 0);
  assert (strcmp (get_parse_tree_node_symbol (ptn_or), get_symbol (s_or)) ==
          0);
  assert (strcmp (get_parse_tree_node_symbol (ptn_and), get_symbol (s_and)) ==
          0);
  assert (strcmp (get_parse_tree_node_symbol (ptn_bor), get_symbol (s_bor)) ==
          0);
  assert (strcmp (get_parse_tree_node_symbol (ptn_bxor), get_symbol (s_bxor))
          == 0);
  assert (strcmp (get_parse_tree_node_symbol (ptn_band), get_symbol (s_band))
          == 0);
  assert (strcmp (get_parse_tree_node_symbol (ptn_eq), get_symbol (s_eq)) ==
          0);
  assert (strcmp (get_parse_tree_node_symbol (ptn_neq), get_symbol (s_neq)) ==
          0);
  assert (strcmp (get_parse_tree_node_symbol (ptn_lt), get_symbol (s_lt)) ==
          0);
  assert (strcmp (get_parse_tree_node_symbol (ptn_lte), get_symbol (s_lte)) ==
          0);
  assert (strcmp (get_parse_tree_node_symbol (ptn_gt), get_symbol (s_gt)) ==
          0);
  assert (strcmp (get_parse_tree_node_symbol (ptn_gte), get_symbol (s_gte)) ==
          0);
  assert (strcmp
          (get_parse_tree_node_symbol (ptn_shiftr),
           get_symbol (s_shiftr)) == 0);
  assert (strcmp
          (get_parse_tree_node_symbol (ptn_shiftl),
           get_symbol (s_shiftl)) == 0);
  assert (strcmp (get_parse_tree_node_symbol (ptn_plus), get_symbol (s_plus))
          == 0);
  assert (strcmp
          (get_parse_tree_node_symbol (ptn_binary_minus),
           get_symbol (s_minus)) == 0);
  assert (strcmp (get_parse_tree_node_symbol (ptn_mult), get_symbol (s_mult))
          == 0);
  assert (strcmp (get_parse_tree_node_symbol (ptn_div), get_symbol (s_div)) ==
          0);
  assert (strcmp (get_parse_tree_node_symbol (ptn_mod), get_symbol (s_mod)) ==
          0);
  assert (strcmp (get_parse_tree_node_symbol (ptn_not), get_symbol (s_not)) ==
          0);
  assert (strcmp (get_parse_tree_node_symbol (ptn_comp), get_symbol (s_comp))
          == 0);
  assert (strcmp
          (get_parse_tree_node_symbol (ptn_unary_minus),
           get_symbol (s_minus)) == 0);
}

void
run_symbol_tests ()
{
  run_test (test_get_symbol);
  run_test (test_get_token_symbol);
  run_test (test_get_parse_tree_node_symbol);
}
