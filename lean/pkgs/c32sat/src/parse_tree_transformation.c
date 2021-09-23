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
#include "memory_management.h"
#include "parse_tree_transformation.h"
#include "aig.h"
#include "aig_vector.h"
#include "hash_table.h"
#include "parse_tree.h"
#include "parse_tree_analysis.h"
#include "config.h"
#include "stack.h"
#include "bool.h"

struct ParseTree2Aig32State
{
  Bool beginning;
  ParseTreeNode *node;
};

typedef struct ParseTree2Aig32State ParseTree2Aig32State;

static ParseTree2Aig32State *
create_parse_tree_2_aig_vector_state (Bool beginning, ParseTreeNode * node)
{
  ParseTree2Aig32State *state = NULL;
  assert (node != NULL);
  state =
    (ParseTree2Aig32State *) malloc_c32sat (sizeof (ParseTree2Aig32State));
  state->beginning = beginning;
  state->node = node;
  return state;
}

static void
delete_parse_tree_2_aig_vector_state (ParseTree2Aig32State * state)
{
  assert (state != NULL);
  free_c32sat (state, sizeof (ParseTree2Aig32State));
}

AIGVector *
parse_tree_2_aig_vector (AIGUniqueTable ** unique_table,
                         ParseTree * tree, HashTable ** symbol_table)
{
  int i = 0;
  AIGVector *result = NULL;
  AIGVector *first = NULL;
  AIGVector *second = NULL;
  AIGVector *third = NULL;
  AIG *temp = NULL;
  VariableContext *context = NULL;
  Stack *stack = NULL;
  Stack *result_stack = NULL;
  ParseTree2Aig32State *state = NULL;
  assert (unique_table != NULL && *unique_table != NULL
          && tree != NULL && tree->root != NULL && symbol_table != NULL);
  stack = create_stack ();
  result_stack = create_stack ();
  push_stack (stack,
              (void *) create_parse_tree_2_aig_vector_state (b_true,
                                                             tree->root));
  while ((state = (ParseTree2Aig32State *) pop_stack (stack)) != NULL)
    {
      first = NULL;
      second = NULL;
      third = NULL;
      result = NULL;
      if (state->beginning)
        {
          assert (state->node != NULL);
          switch (state->node->kind)
            {
            case ptn_ident:
              result = create_aig_vector ();
              context =
                (VariableContext *) lookup_hash_table (symbol_table,
                                                       state->node->core.str);
              if (context->bool)
                {
                  result->aig[0] = var_aig (unique_table, context->start_id);
                }
              else
                {
                  if (ext_app_mode == am_sat_ua)
                    {
                      for (i = 0; i < ext_approx_number_of_bits; i++)
                        {
                          result->aig[i] =
                            var_aig (unique_table, i + context->start_id);
                        }
                      if (ext_approx_number_of_bits < ext_number_of_bits)
                        {
                          temp =
                            var_aig (unique_table,
                                     ext_approx_number_of_bits +
                                     context->start_id);
                          for (i = ext_approx_number_of_bits;
                               i < ext_number_of_bits; i++)
                            {
                              result->aig[i] = copy_aig (unique_table, temp);
                            }
                          release_aig (unique_table, temp);
                        }
                    }
                  else
                    {
                      for (i = 0; i < ext_number_of_bits; i++)
                        {
                          result->aig[i] =
                            var_aig (unique_table, i + context->start_id);
                        }
                    }
                }
              push_stack (result_stack, (void *) result);
              break;
            case ptn_integer:
              result = create_aig_vector ();
              long_long_2_aig_vector (state->node->core.val, result);
              push_stack (result_stack, (void *) result);
              break;
              /* ternary operator */
            case ptn_qm:
              push_stack (stack,
                          (void *)
                          create_parse_tree_2_aig_vector_state (b_false,
                                                                state->node));
              push_stack (stack,
                          (void *)
                          create_parse_tree_2_aig_vector_state (b_true,
                                                                parse_tree_node_third_child
                                                                (state->
                                                                 node)));
              push_stack (stack,
                          (void *)
                          create_parse_tree_2_aig_vector_state (b_true,
                                                                parse_tree_node_second_child
                                                                (state->
                                                                 node)));
              push_stack (stack,
                          (void *)
                          create_parse_tree_2_aig_vector_state (b_true,
                                                                parse_tree_node_first_child
                                                                (state->
                                                                 node)));
              break;
              /* unary operators */
            case ptn_not:
            case ptn_comp:
            case ptn_unary_minus:
              push_stack (stack,
                          (void *)
                          create_parse_tree_2_aig_vector_state (b_false,
                                                                state->node));
              push_stack (stack,
                          (void *)
                          create_parse_tree_2_aig_vector_state (b_true,
                                                                parse_tree_node_first_child
                                                                (state->
                                                                 node)));
              break;
              /* binary operators */
            default:
              push_stack (stack,
                          (void *)
                          create_parse_tree_2_aig_vector_state (b_false,
                                                                state->node));
              push_stack (stack,
                          (void *)
                          create_parse_tree_2_aig_vector_state (b_true,
                                                                parse_tree_node_second_child
                                                                (state->
                                                                 node)));
              push_stack (stack,
                          (void *)
                          create_parse_tree_2_aig_vector_state (b_true,
                                                                parse_tree_node_first_child
                                                                (state->
                                                                 node)));
              break;
            }
        }
      else
        {
          switch (state->node->kind)
            {
            case ptn_dimp:
              second = (AIGVector *) pop_stack (result_stack);
              first = (AIGVector *) pop_stack (result_stack);
              result = dimp_aig_vector (unique_table, first, second);
              break;
            case ptn_imp:
              second = (AIGVector *) pop_stack (result_stack);
              first = (AIGVector *) pop_stack (result_stack);
              result = imp_aig_vector (unique_table, first, second);
              break;
            case ptn_or:
              second = (AIGVector *) pop_stack (result_stack);
              first = (AIGVector *) pop_stack (result_stack);
              result = or_aig_vector (unique_table, first, second);
              break;
            case ptn_and:
              second = (AIGVector *) pop_stack (result_stack);
              first = (AIGVector *) pop_stack (result_stack);
              result = and_aig_vector (unique_table, first, second);
              break;
            case ptn_not:
              first = (AIGVector *) pop_stack (result_stack);
              result = not_aig_vector (unique_table, first);
              break;
            case ptn_comp:
              first = (AIGVector *) pop_stack (result_stack);
              result = copy_aig_vector (unique_table, first);
              invert_aig_vector (result);
              break;
            case ptn_band:
              second = (AIGVector *) pop_stack (result_stack);
              first = (AIGVector *) pop_stack (result_stack);
              result = band_aig_vector (unique_table, first, second);
              break;
            case ptn_bor:
              second = (AIGVector *) pop_stack (result_stack);
              first = (AIGVector *) pop_stack (result_stack);
              result = bor_aig_vector (unique_table, first, second);
              break;
            case ptn_bxor:
              second = (AIGVector *) pop_stack (result_stack);
              first = (AIGVector *) pop_stack (result_stack);
              result = bxor_aig_vector (unique_table, first, second);
              break;
            case ptn_unary_minus:
              first = (AIGVector *) pop_stack (result_stack);
              result = unary_minus_aig_vector (unique_table, first);
              break;
            case ptn_binary_minus:
              second = (AIGVector *) pop_stack (result_stack);
              first = (AIGVector *) pop_stack (result_stack);
              result = subtract_aig_vector (unique_table, first, second);
              break;
            case ptn_plus:
              second = (AIGVector *) pop_stack (result_stack);
              first = (AIGVector *) pop_stack (result_stack);
              result = add_aig_vector (unique_table, first, second);
              break;
            case ptn_eq:
              second = (AIGVector *) pop_stack (result_stack);
              first = (AIGVector *) pop_stack (result_stack);
              result = eq_aig_vector (unique_table, first, second);
              break;
            case ptn_neq:
              second = (AIGVector *) pop_stack (result_stack);
              first = (AIGVector *) pop_stack (result_stack);
              result = neq_aig_vector (unique_table, first, second);
              break;
            case ptn_lt:
              second = (AIGVector *) pop_stack (result_stack);
              first = (AIGVector *) pop_stack (result_stack);
              result = less_than_aig_vector (unique_table, first, second);
              break;
            case ptn_lte:
              second = (AIGVector *) pop_stack (result_stack);
              first = (AIGVector *) pop_stack (result_stack);
              result =
                less_than_or_equal_aig_vector (unique_table, first, second);
              break;
            case ptn_gt:
              second = (AIGVector *) pop_stack (result_stack);
              first = (AIGVector *) pop_stack (result_stack);
              result = greater_than_aig_vector (unique_table, first, second);
              break;
            case ptn_gte:
              second = (AIGVector *) pop_stack (result_stack);
              first = (AIGVector *) pop_stack (result_stack);
              result =
                greater_than_or_equal_aig_vector (unique_table, first,
                                                  second);
              break;
            case ptn_shiftl:
              second = (AIGVector *) pop_stack (result_stack);
              first = (AIGVector *) pop_stack (result_stack);
              result = shift_left_aig_vector (unique_table, first, second);
              break;
            case ptn_shiftr:
              second = (AIGVector *) pop_stack (result_stack);
              first = (AIGVector *) pop_stack (result_stack);
              result = shift_right_aig_vector (unique_table, first, second);
              break;
            case ptn_mult:
              second = (AIGVector *) pop_stack (result_stack);
              first = (AIGVector *) pop_stack (result_stack);
              result = multiply_aig_vector (unique_table, first, second);
              break;
            case ptn_div:
              second = (AIGVector *) pop_stack (result_stack);
              first = (AIGVector *) pop_stack (result_stack);
              result = divide_aig_vector (unique_table, first, second);
              break;
            case ptn_mod:
              second = (AIGVector *) pop_stack (result_stack);
              first = (AIGVector *) pop_stack (result_stack);
              result = modulo_aig_vector (unique_table, first, second);
              break;
            case ptn_qm:
              third = (AIGVector *) pop_stack (result_stack);
              second = (AIGVector *) pop_stack (result_stack);
              first = (AIGVector *) pop_stack (result_stack);
              result =
                if_then_else_aig_vector (unique_table, first, second, third);
              break;
            default:
              assert (0);
              break;
            }
          assert (!(first == NULL && second == NULL && third == NULL));
          if (first != NULL)
            {
              release_aig_vector (unique_table, first);
              delete_aig_vector (first);
            }
          if (second != NULL)
            {
              release_aig_vector (unique_table, second);
              delete_aig_vector (second);
            }
          if (third != NULL)
            {
              release_aig_vector (unique_table, third);
              delete_aig_vector (third);
            }
          assert (result != NULL);
          push_stack (result_stack, (void *) result);
        }
      delete_parse_tree_2_aig_vector_state (state);
    }
  result = (AIGVector *) pop_stack (result_stack);
  assert (is_empty_stack (result_stack));
  delete_stack (result_stack);
  delete_stack (stack);
  return result;
}
