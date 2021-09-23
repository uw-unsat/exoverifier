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
#include <string.h>
#include "config.h"
#include "bool.h"
#include "parse_tree_analysis.h"
#include "parse_tree.h"
#include "hash_table.h"
#include "linked_list.h"
#include "memory_management.h"
#include "error_management.h"
#include "stack.h"

static unsigned int
g_primes [] =
{
  2000000011,
  2000000033,
  2000000063,
  2000000087,
  2000000089,
  2000000099,
  2000000137,
  2000000141,
  2000000143,
  2000000153,
};

#define PARSE_TREE_ANALYSIS_NUM_PRIMES 10

#define PARSE_TREE_ANALYSIS_INITIAL_SYMBOL_TABLE_POWER 10

#define is_bool_operator(node) ((node)->kind == ptn_dimp || (node)->kind == ptn_imp || (node)->kind == ptn_and || (node)->kind == ptn_or || (node)->kind == ptn_not)

static VariableContext *
create_variable_context (Bool bool, int start_id)
{
  VariableContext *context = NULL;
  assert (start_id > 0);
  context = (VariableContext *) malloc_c32sat (sizeof (VariableContext));
  context->bool = bool;
  context->start_id = start_id;
  return context;
}

static void
delete_variable_context (VariableContext * context)
{
  assert (context != NULL);
  free_c32sat (context, sizeof (VariableContext));
}

static unsigned int
primes_string_hash (void * str)
{
  unsigned int res = 0; 
  unsigned int i = 0;
  const char * p = NULL;
  for (p = (char *)str; *p; p++)
    {
      res += *p * g_primes[i++];
      if (i >= PARSE_TREE_ANALYSIS_NUM_PRIMES)
        {
          i = 0;
        }
    }
  return res;
}

static Bool
equals_string (void *string1, void *string2)
{
  if (strcmp ((char *) string1, (char *) string2) == 0)
    {
      return b_true;
    }
  return b_false;
}

static void
destroy_variable_context (void *data)
{
  delete_variable_context ((VariableContext *) data);
}

static void
analyse_variable (char *variable, Bool bool, HashTable ** table,
                  LinkedList * var_list)
{
  char *string_copy = NULL;
  VariableContext *context = NULL;
  assert (variable != NULL && table != NULL);
  context = (VariableContext *) lookup_hash_table (table, (void *) variable);
  if (context == NULL)
    {
      if (var_list->size == ext_number_of_supported_variables)
        {
          if (!ext_too_many_variables_error_occured)
            {
              error (e_parse_tree_analysis_too_many_variables, 0, 0,
                     ext_number_of_supported_variables, NULL);
            }
        }
      else
        {
          string_copy =
            (char *) malloc_c32sat (sizeof (char) * (strlen (variable) + 1));
          strcpy (string_copy, variable);
          context = create_variable_context (bool, 1);
          insert_data_hash_table (table, (void *) string_copy,
                                  (void *) context);
          add_element_last_linked_list (var_list, string_copy);
        }
    }
  else
    {
      if (context->bool && !bool)
        {
          context->bool = b_false;
        }
    }
}

struct ParseTreeAnalysisState
{
  ParseTreeNode *node;
  ParseTreeNode *parent_node;
};

typedef struct ParseTreeAnalysisState ParseTreeAnalysisState;

static ParseTreeAnalysisState *
create_parse_tree_analysis_state (ParseTreeNode * node,
                                  ParseTreeNode * parent_node)
{
  ParseTreeAnalysisState *state = NULL;
  assert (node != NULL);
  state =
    (ParseTreeAnalysisState *)
    malloc_c32sat (sizeof (ParseTreeAnalysisState));
  state->node = node;
  state->parent_node = parent_node;
  return state;
}

static void
delete_parse_tree_analysis_state (ParseTreeAnalysisState * state)
{
  assert (state != NULL);
  free_c32sat (state, sizeof (ParseTreeAnalysisState));
}

HashTable *
analyse_parse_tree (ParseTree * tree, LinkedList ** variables,
                    int *first_free_id)
{
  HashTable *table = NULL;
  LinkedList *var_list = NULL;
  LinkedListIterator *iterator = NULL;
  Stack *stack = NULL;
  VariableContext *context = NULL;
  ParseTreeAnalysisState *state = NULL;
  int cur_id = 1;
  assert (tree != NULL && tree->root != NULL && variables != NULL
          && first_free_id != NULL);
  table =
    create_hash_table (PARSE_TREE_ANALYSIS_INITIAL_SYMBOL_TABLE_POWER,
                       primes_string_hash, equals_string,
                       destroy_variable_context);
  var_list = create_linked_list ();
  stack = create_stack ();
  push_stack (stack,
              (void *) create_parse_tree_analysis_state (tree->root, NULL));
  while ((state = (ParseTreeAnalysisState *) pop_stack (stack)) != NULL)
    {
      switch (state->node->kind)
        {
          /* Leaves */
        case ptn_ident:
          if (state->parent_node == NULL)
            {
              analyse_variable (state->node->core.str, b_true, &table,
                                var_list);
            }
          else if (is_bool_operator (state->parent_node))
            {
              analyse_variable (state->node->core.str, b_true, &table,
                                var_list);
            }
          else
            {
              analyse_variable (state->node->core.str, b_false, &table,
                                var_list);
            }
          break;
        case ptn_integer:
          break;
          /* Ternary operator */
        case ptn_qm:
          push_stack (stack,
                      (void *)
                      create_parse_tree_analysis_state
                      (parse_tree_node_third_child (state->node),
                       state->node));
          push_stack (stack,
                      (void *)
                      create_parse_tree_analysis_state
                      (parse_tree_node_second_child (state->node),
                       state->node));
          push_stack (stack,
                      (void *)
                      create_parse_tree_analysis_state
                      (parse_tree_node_first_child (state->node),
                       state->node));
          break;
          /* Unary Operators */
        case ptn_not:
        case ptn_comp:
        case ptn_unary_minus:
          push_stack (stack,
                      (void *)
                      create_parse_tree_analysis_state
                      (parse_tree_node_first_child (state->node),
                       state->node));
          break;
          /* Binary operators */
        default:
          push_stack (stack,
                      (void *)
                      create_parse_tree_analysis_state
                      (parse_tree_node_second_child (state->node),
                       state->node));
          push_stack (stack,
                      (void *)
                      create_parse_tree_analysis_state
                      (parse_tree_node_first_child (state->node),
                       state->node));
          break;
        }
      delete_parse_tree_analysis_state (state);
    }
  iterator = create_linked_list_iterator (var_list);
  assert (!ext_too_many_aigs_error_occured);
  while (has_next_linked_list_iterator (iterator))
    {
      context =
        (VariableContext *) lookup_hash_table (&table,
                                               next_linked_list_iterator
                                               (iterator));
      assert (context != NULL);
      if (!ext_too_many_aigs_error_occured)
        {
          if (context->bool)
            {
              if (ext_number_of_supported_aigs - cur_id < 0)
                {
                  error (e_aig_too_many_aigs, 0, 0,
                         ext_number_of_supported_aigs, NULL);
                }
              else
                {
                  context->start_id = cur_id++;
                }
            }
          else
            {
              if (ext_app_mode == am_sat_ua)
                {
                  if (ext_number_of_supported_aigs -
                      (cur_id + ext_approx_number_of_bits) < 0)
                    {
                      error (e_aig_too_many_aigs, 0, 0,
                             ext_number_of_supported_aigs, NULL);
                    }
                  else
                    {
                      context->start_id = cur_id;
                      cur_id += ext_approx_number_of_bits + 1;
                    }
                }
              else
                {
                  if (ext_number_of_supported_aigs -
                      (cur_id + ext_number_of_bits - 1) < 0)
                    {
                      error (e_aig_too_many_aigs, 0, 0,
                             ext_number_of_supported_aigs, NULL);
                    }
                  else
                    {
                      context->start_id = cur_id;
                      cur_id += ext_number_of_bits;
                    }
                }
            }
        }
    }
  *variables = var_list;
  *first_free_id = cur_id;
  delete_linked_list_iterator (iterator);
  delete_stack (stack);
  return table;
}
