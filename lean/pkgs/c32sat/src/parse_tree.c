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
#include "bool.h"
#include "stack.h"
#include "parse_tree.h"
#include "symbol.h"
#include "memory_management.h"

static unsigned long long int g_par_level;

ParseTreeNode *
create_parse_tree_node (ParseTreeNodeKind kind)
{
  ParseTreeNode *node = NULL;
  assert (kind != ptn_ident && kind != ptn_integer);
  node = (ParseTreeNode *) malloc_c32sat (sizeof (ParseTreeNode));
  node->kind = kind;
  parse_tree_node_first_child (node) = NULL;
  parse_tree_node_second_child (node) = NULL;
  parse_tree_node_third_child (node) = NULL;
  return node;
}

ParseTreeNode *
create_parse_tree_ident_leaf (const char *str)
{
  ParseTreeNode *node = NULL;
  assert (str != NULL);
  node = (ParseTreeNode *) malloc_c32sat (sizeof (ParseTreeNode));
  node->kind = ptn_ident;
  node->core.str =
    (char *) malloc_c32sat (sizeof (char) * (strlen (str) + 1));
  strcpy (node->core.str, str);
  return node;
}

ParseTreeNode *
create_parse_tree_integer_leaf (long long int val)
{
  ParseTreeNode *node = NULL;
  assert (val >= 0);
  node = (ParseTreeNode *) malloc_c32sat (sizeof (ParseTreeNode));
  node->kind = ptn_integer;
  node->core.val = val;
  return node;
}

static void
delete_parse_tree_node_internal (ParseTreeNode * node)
{
  assert (node != NULL);
  if (node->kind == ptn_ident)
    {
      free_c32sat (node->core.str,
                   sizeof (char) * (strlen (node->core.str) + 1));
    }
  free_c32sat (node, sizeof (ParseTreeNode));
}

ParseTree *
create_parse_tree ()
{
  ParseTree *tree = NULL;
  tree = (ParseTree *) malloc_c32sat (sizeof (ParseTree));
  tree->root = NULL;
  return tree;
}

struct ParseTreeDeleteState
{
  Bool beginning;
  ParseTreeNode *node;
};

typedef struct ParseTreeDeleteState ParseTreeDeleteState;

static ParseTreeDeleteState *
create_parse_tree_delete_state (Bool beginning, ParseTreeNode * node)
{
  ParseTreeDeleteState *state =
    (ParseTreeDeleteState *) malloc_c32sat (sizeof (ParseTreeDeleteState));
  state->beginning = beginning;
  state->node = node;
  return state;
}

static void
delete_parse_tree_delete_state (ParseTreeDeleteState * state)
{
  assert (state != NULL);
  free_c32sat (state, sizeof (ParseTreeDeleteState));
}

void
delete_parse_tree_node (ParseTreeNode * node)
{
  Stack *stack = NULL;
  ParseTreeDeleteState *state = NULL;
  stack = create_stack ();
  push_stack (stack, (void *) create_parse_tree_delete_state (b_true, node));
  while ((state = (ParseTreeDeleteState *) pop_stack (stack)) != NULL)
    {
      if (state->node != NULL)
        {
          if (state->beginning)
            {
              switch (state->node->kind)
                {
                  /* Leaves */
                case ptn_ident:
                case ptn_integer:
                  delete_parse_tree_node_internal (state->node);
                  break;
                  /* Ternary operator */
                case ptn_qm:
                  push_stack (stack,
                              (void *)
                              create_parse_tree_delete_state (b_false,
                                                              state->node));
                  push_stack (stack,
                              (void *) create_parse_tree_delete_state (b_true,
                                                                       parse_tree_node_third_child
                                                                       (state->
                                                                        node)));
                  push_stack (stack,
                              (void *) create_parse_tree_delete_state (b_true,
                                                                       parse_tree_node_second_child
                                                                       (state->
                                                                        node)));
                  push_stack (stack,
                              (void *) create_parse_tree_delete_state (b_true,
                                                                       parse_tree_node_first_child
                                                                       (state->
                                                                        node)));
                  break;
                  /* Unary Operators */
                case ptn_not:
                case ptn_comp:
                case ptn_unary_minus:
                  push_stack (stack,
                              (void *)
                              create_parse_tree_delete_state (b_false,
                                                              state->node));
                  push_stack (stack,
                              (void *) create_parse_tree_delete_state (b_true,
                                                                       parse_tree_node_first_child
                                                                       (state->
                                                                        node)));
                  break;
                  /* Binary operators */
                default:
                  push_stack (stack,
                              (void *)
                              create_parse_tree_delete_state (b_false,
                                                              state->node));
                  push_stack (stack,
                              (void *) create_parse_tree_delete_state (b_true,
                                                                       parse_tree_node_second_child
                                                                       (state->
                                                                        node)));
                  push_stack (stack,
                              (void *) create_parse_tree_delete_state (b_true,
                                                                       parse_tree_node_first_child
                                                                       (state->
                                                                        node)));
                  break;
                }
            }
          else
            {
              delete_parse_tree_node_internal (state->node);
            }
        }
      delete_parse_tree_delete_state (state);
    }
  delete_stack (stack);
}

void
delete_parse_tree (ParseTree * tree)
{
  if (tree->root != NULL)
    {
      delete_parse_tree_node (tree->root);
    }
  free_c32sat (tree, sizeof (ParseTree));
}

enum OpClassPriority
{
  ocp_qm = 1,
  ocp_imp,
  ocp_or,
  ocp_and,
  ocp_bor,
  ocp_bxor,
  ocp_band,
  ocp_eq,
  ocp_rel,
  ocp_shift,
  ocp_add,
  ocp_mult,
  ocp_not
};

typedef enum OpClassPriority OpClassPriority;

static OpClassPriority
get_op_class_priority (ParseTreeNodeKind kind)
{
  int result = -1;
  assert (kind != ptn_ident && kind != ptn_integer);
  switch (kind)
    {
    case ptn_qm:
      result = ocp_qm;
      break;
    case ptn_imp:
    case ptn_dimp:
      result = ocp_imp;
      break;
    case ptn_or:
      result = ocp_or;
      break;
    case ptn_and:
      result = ocp_and;
      break;
    case ptn_bor:
      result = ocp_bor;
      break;
    case ptn_bxor:
      result = ocp_bxor;
      break;
    case ptn_band:
      result = ocp_band;
      break;
    case ptn_eq:
    case ptn_neq:
      result = ocp_eq;
      break;
    case ptn_lt:
    case ptn_lte:
    case ptn_gt:
    case ptn_gte:
      result = ocp_rel;
      break;
    case ptn_shiftr:
    case ptn_shiftl:
      result = ocp_shift;
      break;
    case ptn_plus:
    case ptn_binary_minus:
      result = ocp_add;
      break;
    case ptn_mult:
    case ptn_div:
    case ptn_mod:
      result = ocp_mult;
      break;
    case ptn_not:
    case ptn_comp:
    case ptn_unary_minus:
      result = ocp_not;
      break;
    default:
      assert (0);
      break;
    }
  return result;
}

enum PrettyPrintStateKind
{
  ppsk_beginning = 0,
  ppsk_middle,
  ppsk_middle1_qm,
  ppsk_middle2_qm,
  ppsk_end
};

typedef enum PrettyPrintStateKind PrettyPrintStateKind;

struct PrettyPrintState
{
  PrettyPrintStateKind kind;
  ParseTreeNode *node;
  ParseTreeNode *parent_node;
  Bool need_par;
};

typedef struct PrettyPrintState PrettyPrintState;

static PrettyPrintState *
create_pretty_print_state (PrettyPrintStateKind kind, ParseTreeNode * node,
                           ParseTreeNode * parent_node, Bool need_par)
{
  PrettyPrintState *state =
    (PrettyPrintState *) malloc_c32sat (sizeof (PrettyPrintState));
  state->kind = kind;
  state->node = node;
  state->parent_node = parent_node;
  state->need_par = need_par;
  return state;
}

static void
delete_pretty_print_state (PrettyPrintState * state)
{
  assert (state != NULL);
  free_c32sat (state, sizeof (PrettyPrintState));
}

void
pretty_print_parse_tree (const ParseTree * tree, FILE * output)
{
  OpClassPriority priority = 0;
  OpClassPriority parent_priority = 0;
  Stack *stack = NULL;
  PrettyPrintState *state = NULL;
  assert (tree != NULL && tree->root != NULL && output != NULL);
  g_par_level = 0;
  stack = create_stack ();
  state =
    create_pretty_print_state (ppsk_beginning, tree->root, NULL, b_false);
  push_stack (stack, state);
  while ((state = (PrettyPrintState *) pop_stack (stack)) != NULL)
    {
      switch (state->kind)
        {
        case ppsk_beginning:
          if (state->node->kind == ptn_ident)
            {
              fprintf (output, "%s", state->node->core.str);
              break;
            }
          if (state->node->kind == ptn_integer)
            {
              fprintf (output, "%lld", state->node->core.val);
              break;
            }
          priority = get_op_class_priority (state->node->kind);
          if (state->parent_node != NULL)
            {
              parent_priority =
                get_op_class_priority (state->parent_node->kind);
              if ((parent_priority > priority)
                  || (parent_priority == priority
                      && state->parent_node->kind == ptn_qm))
                {
                  state->need_par = b_true;
                }
              else if (parent_priority == priority
                       && parse_tree_node_second_child (state->parent_node) ==
                       state->node)
                {
                  switch (state->parent_node->kind)
                    {
                    case ptn_imp:
                      state->need_par = b_true;
                      break;
                    case ptn_dimp:
                      if (state->node->kind == ptn_imp)
                        {
                          state->need_par = b_true;
                        }
                      break;
                    case ptn_mult:
                      if (state->node->kind != ptn_mult)
                        {
                          state->need_par = b_true;
                        }
                      break;
                    case ptn_eq:
                    case ptn_neq:
                    case ptn_lt:
                    case ptn_lte:
                    case ptn_gt:
                    case ptn_gte:
                    case ptn_shiftl:
                    case ptn_shiftr:
                    case ptn_binary_minus:
                    case ptn_div:
                    case ptn_mod:
                      state->need_par = b_true;
                      break;
                    default:
                      break;
                    }
                }
            }
          if (state->need_par)
            {
              fprintf (output, "%s", get_symbol (s_lpar));
              g_par_level++;
            }
          switch (state->node->kind)
            {
            case ptn_qm:
              push_stack (stack,
                          (void *) create_pretty_print_state (ppsk_end, NULL,
                                                              NULL,
                                                              state->
                                                              need_par));
              push_stack (stack,
                          (void *) create_pretty_print_state (ppsk_beginning,
                                                              parse_tree_node_third_child
                                                              (state->node),
                                                              state->node,
                                                              b_false));
              push_stack (stack,
                          (void *) create_pretty_print_state (ppsk_middle2_qm,
                                                              NULL, NULL,
                                                              b_false));
              push_stack (stack,
                          (void *) create_pretty_print_state (ppsk_beginning,
                                                              parse_tree_node_second_child
                                                              (state->node),
                                                              state->node,
                                                              b_false));
              push_stack (stack,
                          (void *) create_pretty_print_state (ppsk_middle1_qm,
                                                              NULL, NULL,
                                                              b_false));
              push_stack (stack,
                          (void *) create_pretty_print_state (ppsk_beginning,
                                                              parse_tree_node_first_child
                                                              (state->node),
                                                              state->node,
                                                              b_false));
              break;
            case ptn_imp:
            case ptn_dimp:
            case ptn_or:
            case ptn_and:
            case ptn_bor:
            case ptn_bxor:
            case ptn_band:
            case ptn_eq:
            case ptn_neq:
            case ptn_lt:
            case ptn_lte:
            case ptn_gt:
            case ptn_gte:
            case ptn_shiftr:
            case ptn_shiftl:
            case ptn_plus:
            case ptn_binary_minus:
            case ptn_mult:
            case ptn_div:
            case ptn_mod:
              push_stack (stack,
                          (void *) create_pretty_print_state (ppsk_end, NULL,
                                                              NULL,
                                                              state->
                                                              need_par));
              push_stack (stack,
                          (void *) create_pretty_print_state (ppsk_beginning,
                                                              parse_tree_node_second_child
                                                              (state->node),
                                                              state->node,
                                                              b_false));
              push_stack (stack,
                          (void *) create_pretty_print_state (ppsk_middle,
                                                              state->node,
                                                              NULL, b_false));
              push_stack (stack,
                          (void *) create_pretty_print_state (ppsk_beginning,
                                                              parse_tree_node_first_child
                                                              (state->node),
                                                              state->node,
                                                              b_false));
              break;
            case ptn_not:
            case ptn_comp:
            case ptn_unary_minus:
              fprintf (output, "%s",
                       get_parse_tree_node_symbol (state->node->kind));
              push_stack (stack,
                          (void *) create_pretty_print_state (ppsk_end, NULL,
                                                              NULL,
                                                              state->
                                                              need_par));
              push_stack (stack,
                          (void *) create_pretty_print_state (ppsk_beginning,
                                                              parse_tree_node_first_child
                                                              (state->node),
                                                              state->node,
                                                              b_false));
              break;
            default:
              assert (0);
              break;
            }
          break;
        case ppsk_middle:
          switch (state->node->kind)
            {
            case ptn_imp:
            case ptn_dimp:
            case ptn_or:
            case ptn_and:
              if (g_par_level == 0)
                {
                  fprintf (output, "\n%s\n",
                           get_parse_tree_node_symbol (state->node->kind));
                }
              else
                {
                  fprintf (output, " %s ",
                           get_parse_tree_node_symbol (state->node->kind));
                }
              break;
            case ptn_bor:
            case ptn_bxor:
            case ptn_band:
            case ptn_eq:
            case ptn_neq:
            case ptn_lt:
            case ptn_lte:
            case ptn_gt:
            case ptn_gte:
            case ptn_shiftr:
            case ptn_shiftl:
            case ptn_plus:
            case ptn_binary_minus:
            case ptn_mult:
            case ptn_div:
            case ptn_mod:
              fprintf (output, " %s ",
                       get_parse_tree_node_symbol (state->node->kind));
              break;
            default:
              assert (0);
              break;
            }
          break;
        case ppsk_middle1_qm:
          if (g_par_level == 0)
            {
              fprintf (output, "\n%s\n", get_parse_tree_node_symbol (ptn_qm));
            }
          else
            {
              fprintf (output, " %s ", get_parse_tree_node_symbol (ptn_qm));
            }
          break;
        case ppsk_middle2_qm:
          if (g_par_level == 0)
            {
              fprintf (output, "\n%s\n", get_symbol (s_colon));
            }
          else
            {
              fprintf (output, " %s ", get_symbol (s_colon));
            }
          break;
        case ppsk_end:
          if (state->need_par)
            {
              fprintf (output, "%s", get_symbol (s_rpar));
              g_par_level--;
            }
          break;
        }
      delete_pretty_print_state (state);
    }
  delete_stack (stack);
  fprintf (output, "\n");
}
