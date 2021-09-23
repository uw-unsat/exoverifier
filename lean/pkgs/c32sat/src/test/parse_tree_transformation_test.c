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
#include <assert.h>
#include <stdlib.h>
#include <string.h>
#include <limits.h>
#include "parse_tree_transformation_test.h"
#include "test_logging.h"
#include "random_utilities.h"
#include "special_operator.h"
#include "../aig.h"
#include "../aig_vector.h"
#include "../parse_tree.h"
#include "../parse_tree_analysis.h"
#include "../parse_tree_transformation.h"
#include "../memory_management.h"
#include "../error_management.h"
#include "../scanner.h"
#include "../parser.h"
#include "../hash_table.h"

#define PARSE_TREE_TRANSFORMATION_TEST_RANDOM_TESTS 500

void
test_parse_tree_2_aig_vector_integer (int x)
{
  ParseTree *tree = NULL;
  ParseTreeNode *unary_minus = NULL;
  HashTable *symbol_table = NULL;
  LinkedList *variables = NULL;
  AIGUniqueTable *unique_table = NULL;
  AIGVector *result = NULL;
  int first_free_id = 0;
  init_error_management (stderr);
  init_memory_management ();
  unique_table = create_aig_unique_table (8);
  tree = create_parse_tree ();
  if (x >= 0)
    {
      tree->root = create_parse_tree_integer_leaf (x);
    }
  else
    {
      unary_minus = create_parse_tree_node (ptn_unary_minus);
      parse_tree_node_first_child (unary_minus) =
        create_parse_tree_integer_leaf (-x);
      tree->root = unary_minus;
    }
  symbol_table = analyse_parse_tree (tree, &variables, &first_free_id);
  result = parse_tree_2_aig_vector (&unique_table, tree, &symbol_table);
  assert (aig_vector_2_long_long (result) == x);
  assert (variables->size == 0);
  delete_linked_list (variables);
  delete_hash_table (symbol_table, b_true);
  delete_parse_tree (tree);
  delete_aig_vector (result);
  delete_aig_unique_table (unique_table, b_false);
  finalise_memory_management ();
}

void
test_parse_tree_2_aig_vector_integer_1 ()
{
  test_parse_tree_2_aig_vector_integer (INT_MAX);
}

void
test_parse_tree_2_aig_vector_integer_2 ()
{
  test_parse_tree_2_aig_vector_integer (INT_MIN + 1);
}

void
test_parse_tree_2_aig_vector_integer_3 ()
{
  test_parse_tree_2_aig_vector_integer (0);
}

void
test_parse_tree_2_aig_vector_integer_4 ()
{
  test_parse_tree_2_aig_vector_integer (1);
}

void
test_parse_tree_2_aig_vector_integer_5 ()
{
  test_parse_tree_2_aig_vector_integer (-1);
}

void
test_parse_tree_2_aig_vector_integer_random ()
{
  run_void_int_function_random (test_parse_tree_2_aig_vector_integer,
                                PARSE_TREE_TRANSFORMATION_TEST_RANDOM_TESTS);
}

void
test_parse_tree_2_aig_vector_unary_op (ParseTreeNodeKind kind, int x,
                                       int result_expected)
{
  ParseTree *tree = NULL;
  ParseTreeNode *op = NULL;
  ParseTreeNode *unary_minus = NULL;
  HashTable *symbol_table = NULL;
  LinkedList *variables = NULL;
  AIGUniqueTable *unique_table = NULL;
  AIGVector *result = NULL;
  int first_free_id = 0;
  init_error_management (stderr);
  init_memory_management ();
  unique_table = create_aig_unique_table (8);
  tree = create_parse_tree ();
  op = create_parse_tree_node (kind);
  if (x >= 0)
    {
      parse_tree_node_first_child (op) = create_parse_tree_integer_leaf (x);
    }
  else
    {
      unary_minus = create_parse_tree_node (ptn_unary_minus);
      parse_tree_node_first_child (unary_minus) =
        create_parse_tree_integer_leaf (-x);
      parse_tree_node_first_child (op) = unary_minus;
    }
  tree->root = op;
  symbol_table = analyse_parse_tree (tree, &variables, &first_free_id);
  result = parse_tree_2_aig_vector (&unique_table, tree, &symbol_table);
  assert (aig_vector_2_long_long (result) == result_expected);
  assert (variables->size == 0);
  delete_linked_list (variables);
  delete_hash_table (symbol_table, b_true);
  delete_parse_tree (tree);
  delete_aig_vector (result);
  delete_aig_unique_table (unique_table, b_false);
  finalise_memory_management ();
}

void
test_parse_tree_2_aig_vector_not (int x)
{
  test_parse_tree_2_aig_vector_unary_op (ptn_not, x, !x);
}

void
test_parse_tree_2_aig_vector_not_1 ()
{
  test_parse_tree_2_aig_vector_not (INT_MAX);
}

void
test_parse_tree_2_aig_vector_not_2 ()
{
  test_parse_tree_2_aig_vector_not (INT_MIN + 1);
}

void
test_parse_tree_2_aig_vector_not_3 ()
{
  test_parse_tree_2_aig_vector_not (0);
}

void
test_parse_tree_2_aig_vector_not_4 ()
{
  test_parse_tree_2_aig_vector_not (1);
}

void
test_parse_tree_2_aig_vector_not_5 ()
{
  test_parse_tree_2_aig_vector_not (-1);
}

void
test_parse_tree_2_aig_vector_not_random ()
{
  run_void_int_function_random (test_parse_tree_2_aig_vector_not,
                                PARSE_TREE_TRANSFORMATION_TEST_RANDOM_TESTS);
}

void
test_parse_tree_2_aig_vector_comp (int x)
{
  test_parse_tree_2_aig_vector_unary_op (ptn_comp, x, ~x);
}

void
test_parse_tree_2_aig_vector_comp_1 ()
{
  test_parse_tree_2_aig_vector_comp (INT_MAX);
}

void
test_parse_tree_2_aig_vector_comp_2 ()
{
  test_parse_tree_2_aig_vector_comp (INT_MIN + 1);
}

void
test_parse_tree_2_aig_vector_comp_3 ()
{
  test_parse_tree_2_aig_vector_comp (0);
}

void
test_parse_tree_2_aig_vector_comp_4 ()
{
  test_parse_tree_2_aig_vector_comp (1);
}

void
test_parse_tree_2_aig_vector_comp_5 ()
{
  test_parse_tree_2_aig_vector_comp (-1);
}

void
test_parse_tree_2_aig_vector_comp_random ()
{
  run_void_int_function_random (test_parse_tree_2_aig_vector_comp,
                                PARSE_TREE_TRANSFORMATION_TEST_RANDOM_TESTS);
}

void
test_parse_tree_2_aig_vector_unary_minus (int x)
{
  test_parse_tree_2_aig_vector_unary_op (ptn_unary_minus, x, -x);
}

void
test_parse_tree_2_aig_vector_unary_minus_1 ()
{
  test_parse_tree_2_aig_vector_unary_minus (INT_MAX);
}

void
test_parse_tree_2_aig_vector_unary_minus_2 ()
{
  test_parse_tree_2_aig_vector_unary_minus (INT_MIN + 1);
}

void
test_parse_tree_2_aig_vector_unary_minus_3 ()
{
  test_parse_tree_2_aig_vector_unary_minus (0);
}

void
test_parse_tree_2_aig_vector_unary_minus_4 ()
{
  test_parse_tree_2_aig_vector_unary_minus (1);
}

void
test_parse_tree_2_aig_vector_unary_minus_5 ()
{
  test_parse_tree_2_aig_vector_unary_minus (-1);
}

void
test_parse_tree_2_aig_vector_unary_minus_random ()
{
  run_void_int_function_random (test_parse_tree_2_aig_vector_unary_minus,
                                PARSE_TREE_TRANSFORMATION_TEST_RANDOM_TESTS);
}

void
test_parse_tree_2_aig_vector_binary_op (ParseTreeNodeKind kind, int x, int y,
                                        int result_expected)
{
  ParseTree *tree = NULL;
  ParseTreeNode *op = NULL;
  ParseTreeNode *unary_minus = NULL;
  HashTable *symbol_table = NULL;
  LinkedList *variables = NULL;
  AIGUniqueTable *unique_table = NULL;
  AIGVector *result = NULL;
  int first_free_id = 0;
  init_error_management (stderr);
  init_memory_management ();
  unique_table = create_aig_unique_table (8);
  tree = create_parse_tree ();
  op = create_parse_tree_node (kind);
  if (x >= 0)
    {
      parse_tree_node_first_child (op) = create_parse_tree_integer_leaf (x);
    }
  else
    {
      unary_minus = create_parse_tree_node (ptn_unary_minus);
      parse_tree_node_first_child (unary_minus) =
        create_parse_tree_integer_leaf (-x);
      parse_tree_node_first_child (op) = unary_minus;
    }
  if (y >= 0)
    {
      parse_tree_node_second_child (op) = create_parse_tree_integer_leaf (y);
    }
  else
    {
      unary_minus = create_parse_tree_node (ptn_unary_minus);
      parse_tree_node_first_child (unary_minus) =
        create_parse_tree_integer_leaf (-y);
      parse_tree_node_second_child (op) = unary_minus;
    }
  tree->root = op;
  symbol_table = analyse_parse_tree (tree, &variables, &first_free_id);
  result = parse_tree_2_aig_vector (&unique_table, tree, &symbol_table);
  assert (aig_vector_2_long_long (result) == result_expected);
  assert (variables->size == 0);
  delete_linked_list (variables);
  delete_hash_table (symbol_table, b_true);
  delete_parse_tree (tree);
  delete_aig_vector (result);
  delete_aig_unique_table (unique_table, b_false);
  finalise_memory_management ();
}

void
test_parse_tree_2_aig_vector_and (int x, int y)
{
  test_parse_tree_2_aig_vector_binary_op (ptn_and, x, y, x && y);
}

void
test_parse_tree_2_aig_vector_and_1 ()
{
  test_parse_tree_2_aig_vector_and (0, 0);
}

void
test_parse_tree_2_aig_vector_and_2 ()
{
  test_parse_tree_2_aig_vector_and (0, 1);
}

void
test_parse_tree_2_aig_vector_and_3 ()
{
  test_parse_tree_2_aig_vector_and (1, 0);
}

void
test_parse_tree_2_aig_vector_and_4 ()
{
  test_parse_tree_2_aig_vector_and (1, 1);
}

void
test_parse_tree_2_aig_vector_and_5 ()
{
  test_parse_tree_2_aig_vector_and (INT_MAX, INT_MIN + 1);
}

void
test_parse_tree_2_aig_vector_and_random ()
{
  run_void_int_int_function_random (test_parse_tree_2_aig_vector_and,
                                    PARSE_TREE_TRANSFORMATION_TEST_RANDOM_TESTS);
}

void
test_parse_tree_2_aig_vector_or (int x, int y)
{
  test_parse_tree_2_aig_vector_binary_op (ptn_or, x, y, x || y);
}

void
test_parse_tree_2_aig_vector_or_1 ()
{
  test_parse_tree_2_aig_vector_or (0, 0);
}

void
test_parse_tree_2_aig_vector_or_2 ()
{
  test_parse_tree_2_aig_vector_or (0, 1);
}

void
test_parse_tree_2_aig_vector_or_3 ()
{
  test_parse_tree_2_aig_vector_or (1, 0);
}

void
test_parse_tree_2_aig_vector_or_4 ()
{
  test_parse_tree_2_aig_vector_or (1, 1);
}

void
test_parse_tree_2_aig_vector_or_5 ()
{
  test_parse_tree_2_aig_vector_or (INT_MAX, INT_MIN + 1);
}

void
test_parse_tree_2_aig_vector_or_random ()
{
  run_void_int_int_function_random (test_parse_tree_2_aig_vector_or,
                                    PARSE_TREE_TRANSFORMATION_TEST_RANDOM_TESTS);
}

void
test_parse_tree_2_aig_vector_imp (int x, int y)
{
  test_parse_tree_2_aig_vector_binary_op (ptn_imp, x, y, !x || y);
}

void
test_parse_tree_2_aig_vector_imp_1 ()
{
  test_parse_tree_2_aig_vector_imp (0, 0);
}

void
test_parse_tree_2_aig_vector_imp_2 ()
{
  test_parse_tree_2_aig_vector_imp (0, 1);
}

void
test_parse_tree_2_aig_vector_imp_3 ()
{
  test_parse_tree_2_aig_vector_imp (1, 0);
}

void
test_parse_tree_2_aig_vector_imp_4 ()
{
  test_parse_tree_2_aig_vector_imp (1, 1);
}

void
test_parse_tree_2_aig_vector_imp_5 ()
{
  test_parse_tree_2_aig_vector_imp (INT_MAX, INT_MIN + 1);
}

void
test_parse_tree_2_aig_vector_imp_random ()
{
  run_void_int_int_function_random (test_parse_tree_2_aig_vector_imp,
                                    PARSE_TREE_TRANSFORMATION_TEST_RANDOM_TESTS);
}

void
test_parse_tree_2_aig_vector_dimp (int x, int y)
{
  test_parse_tree_2_aig_vector_binary_op (ptn_dimp, x, y, (!x || y)
                                          && (x || !y));
}

void
test_parse_tree_2_aig_vector_dimp_1 ()
{
  test_parse_tree_2_aig_vector_dimp (0, 0);
}

void
test_parse_tree_2_aig_vector_dimp_2 ()
{
  test_parse_tree_2_aig_vector_dimp (0, 1);
}

void
test_parse_tree_2_aig_vector_dimp_3 ()
{
  test_parse_tree_2_aig_vector_dimp (1, 0);
}

void
test_parse_tree_2_aig_vector_dimp_4 ()
{
  test_parse_tree_2_aig_vector_dimp (1, 1);
}

void
test_parse_tree_2_aig_vector_dimp_5 ()
{
  test_parse_tree_2_aig_vector_dimp (INT_MAX, INT_MIN + 1);
}

void
test_parse_tree_2_aig_vector_dimp_random ()
{
  run_void_int_int_function_random (test_parse_tree_2_aig_vector_dimp,
                                    PARSE_TREE_TRANSFORMATION_TEST_RANDOM_TESTS);
}

void
test_parse_tree_2_aig_vector_band (int x, int y)
{
  test_parse_tree_2_aig_vector_binary_op (ptn_band, x, y, x & y);
}

void
test_parse_tree_2_aig_vector_band_1 ()
{
  test_parse_tree_2_aig_vector_band (0, 0);
}

void
test_parse_tree_2_aig_vector_band_2 ()
{
  test_parse_tree_2_aig_vector_band (0, 1);
}

void
test_parse_tree_2_aig_vector_band_3 ()
{
  test_parse_tree_2_aig_vector_band (1, 0);
}

void
test_parse_tree_2_aig_vector_band_4 ()
{
  test_parse_tree_2_aig_vector_band (1, 1);
}

void
test_parse_tree_2_aig_vector_band_5 ()
{
  test_parse_tree_2_aig_vector_band (INT_MAX, INT_MIN + 1);
}

void
test_parse_tree_2_aig_vector_band_random ()
{
  run_void_int_int_function_random (test_parse_tree_2_aig_vector_band,
                                    PARSE_TREE_TRANSFORMATION_TEST_RANDOM_TESTS);
}

void
test_parse_tree_2_aig_vector_bor (int x, int y)
{
  test_parse_tree_2_aig_vector_binary_op (ptn_bor, x, y, x | y);
}

void
test_parse_tree_2_aig_vector_bor_1 ()
{
  test_parse_tree_2_aig_vector_bor (0, 0);
}

void
test_parse_tree_2_aig_vector_bor_2 ()
{
  test_parse_tree_2_aig_vector_bor (0, 1);
}

void
test_parse_tree_2_aig_vector_bor_3 ()
{
  test_parse_tree_2_aig_vector_bor (1, 0);
}

void
test_parse_tree_2_aig_vector_bor_4 ()
{
  test_parse_tree_2_aig_vector_bor (1, 1);
}

void
test_parse_tree_2_aig_vector_bor_5 ()
{
  test_parse_tree_2_aig_vector_bor (INT_MAX, INT_MIN + 1);
}

void
test_parse_tree_2_aig_vector_bor_random ()
{
  run_void_int_int_function_random (test_parse_tree_2_aig_vector_bor,
                                    PARSE_TREE_TRANSFORMATION_TEST_RANDOM_TESTS);
}

void
test_parse_tree_2_aig_vector_bxor (int x, int y)
{
  test_parse_tree_2_aig_vector_binary_op (ptn_bxor, x, y, x ^ y);
}

void
test_parse_tree_2_aig_vector_bxor_1 ()
{
  test_parse_tree_2_aig_vector_bxor (0, 0);
}

void
test_parse_tree_2_aig_vector_bxor_2 ()
{
  test_parse_tree_2_aig_vector_bxor (0, 1);
}

void
test_parse_tree_2_aig_vector_bxor_3 ()
{
  test_parse_tree_2_aig_vector_bxor (1, 0);
}

void
test_parse_tree_2_aig_vector_bxor_4 ()
{
  test_parse_tree_2_aig_vector_bxor (1, 1);
}

void
test_parse_tree_2_aig_vector_bxor_5 ()
{
  test_parse_tree_2_aig_vector_bxor (INT_MAX, INT_MIN + 1);
}

void
test_parse_tree_2_aig_vector_bxor_random ()
{
  run_void_int_int_function_random (test_parse_tree_2_aig_vector_bxor,
                                    PARSE_TREE_TRANSFORMATION_TEST_RANDOM_TESTS);
}

void
test_parse_tree_2_aig_vector_plus (int x, int y)
{
  test_parse_tree_2_aig_vector_binary_op (ptn_plus, x, y,
                                          add_special_operator (x, y, 32));
}

void
test_parse_tree_2_aig_vector_plus_1 ()
{
  test_parse_tree_2_aig_vector_plus (INT_MIN + 1, INT_MIN + 1);
}

void
test_parse_tree_2_aig_vector_plus_2 ()
{
  test_parse_tree_2_aig_vector_plus (INT_MIN + 1, INT_MAX);
}

void
test_parse_tree_2_aig_vector_plus_3 ()
{
  test_parse_tree_2_aig_vector_plus (INT_MAX, INT_MIN + 1);
}

void
test_parse_tree_2_aig_vector_plus_4 ()
{
  test_parse_tree_2_aig_vector_plus (INT_MAX, INT_MAX);
}

void
test_parse_tree_2_aig_vector_plus_5 ()
{
  test_parse_tree_2_aig_vector_plus (INT_MAX, 0);
}

void
test_parse_tree_2_aig_vector_plus_random ()
{
  run_void_int_int_function_random (test_parse_tree_2_aig_vector_plus,
                                    PARSE_TREE_TRANSFORMATION_TEST_RANDOM_TESTS);
}

void
test_parse_tree_2_aig_vector_binary_minus (int x, int y)
{
  test_parse_tree_2_aig_vector_binary_op (ptn_binary_minus, x, y,
                                          subtract_special_operator (x, y,
                                                                     32));
}

void
test_parse_tree_2_aig_vector_binary_minus_1 ()
{
  test_parse_tree_2_aig_vector_binary_minus (INT_MIN + 1, INT_MIN + 1);
}

void
test_parse_tree_2_aig_vector_binary_minus_2 ()
{
  test_parse_tree_2_aig_vector_binary_minus (INT_MIN + 1, INT_MAX);
}

void
test_parse_tree_2_aig_vector_binary_minus_3 ()
{
  test_parse_tree_2_aig_vector_binary_minus (INT_MAX, INT_MIN + 1);
}

void
test_parse_tree_2_aig_vector_binary_minus_4 ()
{
  test_parse_tree_2_aig_vector_binary_minus (INT_MAX, INT_MAX);
}

void
test_parse_tree_2_aig_vector_binary_minus_5 ()
{
  test_parse_tree_2_aig_vector_binary_minus (INT_MAX, 0);
}

void
test_parse_tree_2_aig_vector_binary_minus_random ()
{
  run_void_int_int_function_random (test_parse_tree_2_aig_vector_binary_minus,
                                    PARSE_TREE_TRANSFORMATION_TEST_RANDOM_TESTS);
}

void
test_parse_tree_2_aig_vector_eq (int x, int y)
{
  test_parse_tree_2_aig_vector_binary_op (ptn_eq, x, y, x == y);
}

void
test_parse_tree_2_aig_vector_eq_1 ()
{
  test_parse_tree_2_aig_vector_eq (INT_MIN + 1, INT_MIN + 1);
}

void
test_parse_tree_2_aig_vector_eq_2 ()
{
  test_parse_tree_2_aig_vector_eq (INT_MIN + 1, INT_MAX);
}

void
test_parse_tree_2_aig_vector_eq_3 ()
{
  test_parse_tree_2_aig_vector_eq (INT_MAX, INT_MIN + 1);
}

void
test_parse_tree_2_aig_vector_eq_4 ()
{
  test_parse_tree_2_aig_vector_eq (INT_MAX, INT_MAX);
}

void
test_parse_tree_2_aig_vector_eq_5 ()
{
  test_parse_tree_2_aig_vector_eq (INT_MAX, 0);
}

void
test_parse_tree_2_aig_vector_eq_random ()
{
  run_void_int_int_function_random (test_parse_tree_2_aig_vector_eq,
                                    PARSE_TREE_TRANSFORMATION_TEST_RANDOM_TESTS);
}

void
test_parse_tree_2_aig_vector_neq (int x, int y)
{
  test_parse_tree_2_aig_vector_binary_op (ptn_neq, x, y, x != y);
}

void
test_parse_tree_2_aig_vector_neq_1 ()
{
  test_parse_tree_2_aig_vector_neq (INT_MIN + 1, INT_MIN + 1);
}

void
test_parse_tree_2_aig_vector_neq_2 ()
{
  test_parse_tree_2_aig_vector_neq (INT_MIN + 1, INT_MAX);
}

void
test_parse_tree_2_aig_vector_neq_3 ()
{
  test_parse_tree_2_aig_vector_neq (INT_MAX, INT_MIN + 1);
}

void
test_parse_tree_2_aig_vector_neq_4 ()
{
  test_parse_tree_2_aig_vector_neq (INT_MAX, INT_MAX);
}

void
test_parse_tree_2_aig_vector_neq_5 ()
{
  test_parse_tree_2_aig_vector_neq (INT_MAX, 0);
}

void
test_parse_tree_2_aig_vector_neq_random ()
{
  run_void_int_int_function_random (test_parse_tree_2_aig_vector_neq,
                                    PARSE_TREE_TRANSFORMATION_TEST_RANDOM_TESTS);
}

void
test_parse_tree_2_aig_vector_lt (int x, int y)
{
  test_parse_tree_2_aig_vector_binary_op (ptn_lt, x, y, x < y);
}

void
test_parse_tree_2_aig_vector_lt_1 ()
{
  test_parse_tree_2_aig_vector_lt (INT_MIN + 1, INT_MIN + 1);
}

void
test_parse_tree_2_aig_vector_lt_2 ()
{
  test_parse_tree_2_aig_vector_lt (INT_MIN + 1, INT_MAX);
}

void
test_parse_tree_2_aig_vector_lt_3 ()
{
  test_parse_tree_2_aig_vector_lt (INT_MAX, INT_MIN + 1);
}

void
test_parse_tree_2_aig_vector_lt_4 ()
{
  test_parse_tree_2_aig_vector_lt (INT_MAX, INT_MAX);
}

void
test_parse_tree_2_aig_vector_lt_5 ()
{
  test_parse_tree_2_aig_vector_lt (INT_MAX, 0);
}

void
test_parse_tree_2_aig_vector_lt_random ()
{
  run_void_int_int_function_random (test_parse_tree_2_aig_vector_lt,
                                    PARSE_TREE_TRANSFORMATION_TEST_RANDOM_TESTS);
}

void
test_parse_tree_2_aig_vector_lte (int x, int y)
{
  test_parse_tree_2_aig_vector_binary_op (ptn_lte, x, y, x <= y);
}

void
test_parse_tree_2_aig_vector_lte_1 ()
{
  test_parse_tree_2_aig_vector_lte (INT_MIN + 1, INT_MIN + 1);
}

void
test_parse_tree_2_aig_vector_lte_2 ()
{
  test_parse_tree_2_aig_vector_lte (INT_MIN + 1, INT_MAX);
}

void
test_parse_tree_2_aig_vector_lte_3 ()
{
  test_parse_tree_2_aig_vector_lte (INT_MAX, INT_MIN + 1);
}

void
test_parse_tree_2_aig_vector_lte_4 ()
{
  test_parse_tree_2_aig_vector_lte (INT_MAX, INT_MAX);
}

void
test_parse_tree_2_aig_vector_lte_5 ()
{
  test_parse_tree_2_aig_vector_lte (INT_MAX, 0);
}

void
test_parse_tree_2_aig_vector_lte_random ()
{
  run_void_int_int_function_random (test_parse_tree_2_aig_vector_lte,
                                    PARSE_TREE_TRANSFORMATION_TEST_RANDOM_TESTS);
}

void
test_parse_tree_2_aig_vector_gt (int x, int y)
{
  test_parse_tree_2_aig_vector_binary_op (ptn_gt, x, y, x > y);
}

void
test_parse_tree_2_aig_vector_gt_1 ()
{
  test_parse_tree_2_aig_vector_gt (INT_MIN + 1, INT_MIN + 1);
}

void
test_parse_tree_2_aig_vector_gt_2 ()
{
  test_parse_tree_2_aig_vector_gt (INT_MIN + 1, INT_MAX);
}

void
test_parse_tree_2_aig_vector_gt_3 ()
{
  test_parse_tree_2_aig_vector_gt (INT_MAX, INT_MIN + 1);
}

void
test_parse_tree_2_aig_vector_gt_4 ()
{
  test_parse_tree_2_aig_vector_gt (INT_MAX, INT_MAX);
}

void
test_parse_tree_2_aig_vector_gt_5 ()
{
  test_parse_tree_2_aig_vector_gt (INT_MAX, 0);
}

void
test_parse_tree_2_aig_vector_gt_random ()
{
  run_void_int_int_function_random (test_parse_tree_2_aig_vector_gt,
                                    PARSE_TREE_TRANSFORMATION_TEST_RANDOM_TESTS);
}

void
test_parse_tree_2_aig_vector_gte (int x, int y)
{
  test_parse_tree_2_aig_vector_binary_op (ptn_gte, x, y, x >= y);
}

void
test_parse_tree_2_aig_vector_gte_1 ()
{
  test_parse_tree_2_aig_vector_gte (INT_MIN + 1, INT_MIN + 1);
}

void
test_parse_tree_2_aig_vector_gte_2 ()
{
  test_parse_tree_2_aig_vector_gte (INT_MIN + 1, INT_MAX);
}

void
test_parse_tree_2_aig_vector_gte_3 ()
{
  test_parse_tree_2_aig_vector_gte (INT_MAX, INT_MIN + 1);
}

void
test_parse_tree_2_aig_vector_gte_4 ()
{
  test_parse_tree_2_aig_vector_gte (INT_MAX, INT_MAX);
}

void
test_parse_tree_2_aig_vector_gte_5 ()
{
  test_parse_tree_2_aig_vector_gte (INT_MAX, 0);
}

void
test_parse_tree_2_aig_vector_gte_random ()
{
  run_void_int_int_function_random (test_parse_tree_2_aig_vector_gte,
                                    PARSE_TREE_TRANSFORMATION_TEST_RANDOM_TESTS);
}

void
test_parse_tree_2_aig_vector_shiftl (int x, int y)
{
  test_parse_tree_2_aig_vector_binary_op (ptn_shiftl, x, y,
                                          shift_left_special_operator (x, y,
                                                                       32));
}

void
test_parse_tree_2_aig_vector_shiftl_1 ()
{
  test_parse_tree_2_aig_vector_shiftl (INT_MIN + 1, INT_MIN + 1);
}

void
test_parse_tree_2_aig_vector_shiftl_2 ()
{
  test_parse_tree_2_aig_vector_shiftl (INT_MIN + 1, INT_MAX);
}

void
test_parse_tree_2_aig_vector_shiftl_3 ()
{
  test_parse_tree_2_aig_vector_shiftl (INT_MAX, INT_MIN + 1);
}

void
test_parse_tree_2_aig_vector_shiftl_4 ()
{
  test_parse_tree_2_aig_vector_shiftl (INT_MAX, INT_MAX);
}

void
test_parse_tree_2_aig_vector_shiftl_5 ()
{
  test_parse_tree_2_aig_vector_shiftl (INT_MAX, 0);
}

void
test_parse_tree_2_aig_vector_shiftl_random ()
{
  run_void_int_int_function_random (test_parse_tree_2_aig_vector_shiftl,
                                    PARSE_TREE_TRANSFORMATION_TEST_RANDOM_TESTS);
}

void
test_parse_tree_2_aig_vector_shiftr (int x, int y)
{
  test_parse_tree_2_aig_vector_binary_op (ptn_shiftr, x, y,
                                          shift_right_special_operator (x, y,
                                                                        32));
}

void
test_parse_tree_2_aig_vector_shiftr_1 ()
{
  test_parse_tree_2_aig_vector_shiftr (INT_MIN + 1, INT_MIN + 1);
}

void
test_parse_tree_2_aig_vector_shiftr_2 ()
{
  test_parse_tree_2_aig_vector_shiftr (INT_MIN + 1, INT_MAX);
}

void
test_parse_tree_2_aig_vector_shiftr_3 ()
{
  test_parse_tree_2_aig_vector_shiftr (INT_MAX, INT_MIN + 1);
}

void
test_parse_tree_2_aig_vector_shiftr_4 ()
{
  test_parse_tree_2_aig_vector_shiftr (INT_MAX, INT_MAX);
}

void
test_parse_tree_2_aig_vector_shiftr_5 ()
{
  test_parse_tree_2_aig_vector_shiftr (INT_MAX, 0);
}

void
test_parse_tree_2_aig_vector_shiftr_random ()
{
  run_void_int_int_function_random (test_parse_tree_2_aig_vector_shiftr,
                                    PARSE_TREE_TRANSFORMATION_TEST_RANDOM_TESTS);
}

void
test_parse_tree_2_aig_vector_multiply (int x, int y)
{
  test_parse_tree_2_aig_vector_binary_op (ptn_mult, x, y,
                                          multiply_special_operator (x, y,
                                                                     32));
}

void
test_parse_tree_2_aig_vector_multiply_1 ()
{
  test_parse_tree_2_aig_vector_multiply (INT_MIN + 1, INT_MIN + 1);
}

void
test_parse_tree_2_aig_vector_multiply_2 ()
{
  test_parse_tree_2_aig_vector_multiply (INT_MIN + 1, INT_MAX);
}

void
test_parse_tree_2_aig_vector_multiply_3 ()
{
  test_parse_tree_2_aig_vector_multiply (INT_MAX, INT_MIN + 1);
}

void
test_parse_tree_2_aig_vector_multiply_4 ()
{
  test_parse_tree_2_aig_vector_multiply (INT_MAX, INT_MAX);
}

void
test_parse_tree_2_aig_vector_multiply_5 ()
{
  test_parse_tree_2_aig_vector_multiply (INT_MAX, 0);
}

void
test_parse_tree_2_aig_vector_multiply_random ()
{
  run_void_int_int_function_random (test_parse_tree_2_aig_vector_multiply,
                                    PARSE_TREE_TRANSFORMATION_TEST_RANDOM_TESTS);
}

void
test_parse_tree_2_aig_vector_divide (int x, int y)
{
  test_parse_tree_2_aig_vector_binary_op (ptn_div, x, y, x / y);
}

void
test_parse_tree_2_aig_vector_divide_1 ()
{
  test_parse_tree_2_aig_vector_divide (INT_MIN + 1, INT_MIN + 1);
}

void
test_parse_tree_2_aig_vector_divide_2 ()
{
  test_parse_tree_2_aig_vector_divide (INT_MIN + 1, INT_MAX);
}

void
test_parse_tree_2_aig_vector_divide_3 ()
{
  test_parse_tree_2_aig_vector_divide (INT_MAX, INT_MIN + 1);
}

void
test_parse_tree_2_aig_vector_divide_4 ()
{
  test_parse_tree_2_aig_vector_divide (INT_MAX, INT_MAX);
}

void
test_parse_tree_2_aig_vector_divide_5 ()
{
  test_parse_tree_2_aig_vector_divide (0, INT_MIN + 1);
}

void
test_parse_tree_2_aig_vector_divide_random ()
{
  run_void_int_int_function_random_second_not_zero
    (test_parse_tree_2_aig_vector_divide,
     PARSE_TREE_TRANSFORMATION_TEST_RANDOM_TESTS);
}

void
test_parse_tree_2_aig_vector_modulo (int x, int y)
{
  test_parse_tree_2_aig_vector_binary_op (ptn_mod, x, y, x % y);
}

void
test_parse_tree_2_aig_vector_modulo_1 ()
{
  test_parse_tree_2_aig_vector_modulo (INT_MIN + 1, INT_MIN + 1);
}

void
test_parse_tree_2_aig_vector_modulo_2 ()
{
  test_parse_tree_2_aig_vector_modulo (INT_MIN + 1, INT_MAX);
}

void
test_parse_tree_2_aig_vector_modulo_3 ()
{
  test_parse_tree_2_aig_vector_modulo (INT_MAX, INT_MIN + 1);
}

void
test_parse_tree_2_aig_vector_modulo_4 ()
{
  test_parse_tree_2_aig_vector_modulo (INT_MAX, INT_MAX);
}

void
test_parse_tree_2_aig_vector_modulo_5 ()
{
  test_parse_tree_2_aig_vector_modulo (0, INT_MIN + 1);
}

void
test_parse_tree_2_aig_vector_modulo_random ()
{
  run_void_int_int_function_random_second_not_zero
    (test_parse_tree_2_aig_vector_modulo,
     PARSE_TREE_TRANSFORMATION_TEST_RANDOM_TESTS);
}

void
test_parse_tree_2_aig_vector_ternary_op (ParseTreeNodeKind kind, int x, int y,
                                         int z, int result_expected)
{
  ParseTree *tree = NULL;
  ParseTreeNode *op = NULL;
  ParseTreeNode *unary_minus = NULL;
  HashTable *symbol_table = NULL;
  LinkedList *variables = NULL;
  AIGUniqueTable *unique_table = NULL;
  AIGVector *result = NULL;
  int first_free_id = 0;
  assert (kind == ptn_qm);
  init_error_management (stderr);
  init_memory_management ();
  unique_table = create_aig_unique_table (8);
  tree = create_parse_tree ();
  op = create_parse_tree_node (kind);
  if (x >= 0)
    {
      parse_tree_node_first_child (op) = create_parse_tree_integer_leaf (x);
    }
  else
    {
      unary_minus = create_parse_tree_node (ptn_unary_minus);
      parse_tree_node_first_child (unary_minus) =
        create_parse_tree_integer_leaf (-x);
      parse_tree_node_first_child (op) = unary_minus;
    }
  if (y >= 0)
    {
      parse_tree_node_second_child (op) = create_parse_tree_integer_leaf (y);
    }
  else
    {
      unary_minus = create_parse_tree_node (ptn_unary_minus);
      parse_tree_node_first_child (unary_minus) =
        create_parse_tree_integer_leaf (-y);
      parse_tree_node_second_child (op) = unary_minus;
    }
  if (z >= 0)
    {
      parse_tree_node_third_child (op) = create_parse_tree_integer_leaf (z);
    }
  else
    {
      unary_minus = create_parse_tree_node (ptn_unary_minus);
      parse_tree_node_first_child (unary_minus) =
        create_parse_tree_integer_leaf (-z);
      parse_tree_node_third_child (op) = unary_minus;
    }
  tree->root = op;
  symbol_table = analyse_parse_tree (tree, &variables, &first_free_id);
  result = parse_tree_2_aig_vector (&unique_table, tree, &symbol_table);
  assert (aig_vector_2_long_long (result) == result_expected);
  assert (variables->size == 0);
  delete_linked_list (variables);
  delete_hash_table (symbol_table, b_true);
  delete_parse_tree (tree);
  delete_aig_vector (result);
  delete_aig_unique_table (unique_table, b_false);
  finalise_memory_management ();
}

void
test_parse_tree_2_aig_vector_if_then_else (int x, int y, int z)
{
  test_parse_tree_2_aig_vector_ternary_op (ptn_qm, x, y, z, x ? y : z);
}

void
test_parse_tree_2_aig_vector_if_then_else_1 ()
{
  test_parse_tree_2_aig_vector_if_then_else (0, 0, 0);
}

void
test_parse_tree_2_aig_vector_if_then_else_2 ()
{
  test_parse_tree_2_aig_vector_if_then_else (0, 0, INT_MAX);
}

void
test_parse_tree_2_aig_vector_if_then_else_3 ()
{
  test_parse_tree_2_aig_vector_if_then_else (0, INT_MAX, 0);
}

void
test_parse_tree_2_aig_vector_if_then_else_4 ()
{
  test_parse_tree_2_aig_vector_if_then_else (INT_MAX, 0, INT_MAX);
}

void
test_parse_tree_2_aig_vector_if_then_else_5 ()
{
  test_parse_tree_2_aig_vector_if_then_else (INT_MAX, INT_MAX, 0);
}

void
test_parse_tree_2_aig_vector_if_then_else_random ()
{
  run_void_int_int_int_function_random
    (test_parse_tree_2_aig_vector_if_then_else,
     PARSE_TREE_TRANSFORMATION_TEST_RANDOM_TESTS);
}

void
test_parse_tree_2_aig_vector_bool_var ()
{
  char *cur_var = NULL;
  ParseTree *tree = NULL;
  HashTable *symbol_table = NULL;
  LinkedList *variables = NULL;
  LinkedListIterator *iterator = NULL;
  AIGUniqueTable *unique_table = NULL;
  AIGVector *result = NULL;
  int i = 0;
  int first_free_id = 0;
  init_error_management (stderr);
  init_memory_management ();
  unique_table = create_aig_unique_table (8);
  tree = create_parse_tree ();
  tree->root = create_parse_tree_ident_leaf ("TEST_IDENT");
  symbol_table = analyse_parse_tree (tree, &variables, &first_free_id);
  result = parse_tree_2_aig_vector (&unique_table, tree, &symbol_table);
  assert (is_aig_var (result->aig[0]));
  for (i = 1; i < 32; i++)
    {
      assert (result->aig[i] == AIG_FALSE);
    }
  assert (variables->size == 1);
  iterator = create_linked_list_iterator (variables);
  while (has_next_linked_list_iterator (iterator))
    {
      cur_var = next_linked_list_iterator (iterator);
      free_c32sat (cur_var, sizeof (char) * (strlen (cur_var) + 1));
    }
  delete_linked_list_iterator (iterator);
  delete_linked_list (variables);
  delete_hash_table (symbol_table, b_true);
  delete_parse_tree (tree);
  release_aig_vector (&unique_table, result);
  delete_aig_vector (result);
  delete_aig_unique_table (unique_table, b_false);
  finalise_memory_management ();
}

void
test_parse_tree_2_aig_vector_32bit_var ()
{
  char *cur_var = NULL;
  ParseTree *tree = NULL;
  HashTable *symbol_table = NULL;
  VariableContext *context = NULL;
  LinkedList *variables = NULL;
  LinkedListIterator *iterator = NULL;
  AIGUniqueTable *unique_table = NULL;
  AIGVector *result = NULL;
  int i = 0;
  int first_free_id = 0;
  init_error_management (stderr);
  init_memory_management ();
  unique_table = create_aig_unique_table (8);
  tree = create_parse_tree ();
  tree->root = create_parse_tree_ident_leaf ("TEST_IDENT");
  symbol_table = analyse_parse_tree (tree, &variables, &first_free_id);
  context =
    (VariableContext *) lookup_hash_table (&symbol_table, "TEST_IDENT");
  assert (context != NULL);
  context->bool = b_false;
  result = parse_tree_2_aig_vector (&unique_table, tree, &symbol_table);
  for (i = 0; i < 32; i++)
    {
      assert (is_aig_var (result->aig[i]));
    }
  assert (variables->size == 1);
  iterator = create_linked_list_iterator (variables);
  while (has_next_linked_list_iterator (iterator))
    {
      cur_var = next_linked_list_iterator (iterator);
      free_c32sat (cur_var, sizeof (char) * (strlen (cur_var) + 1));
    }
  delete_linked_list_iterator (iterator);
  delete_linked_list (variables);
  delete_hash_table (symbol_table, b_true);
  delete_parse_tree (tree);
  release_aig_vector (&unique_table, result);
  delete_aig_vector (result);
  delete_aig_unique_table (unique_table, b_false);
  finalise_memory_management ();
}

void
run_parse_tree_transformation_tests ()
{
  run_test (test_parse_tree_2_aig_vector_integer_1);
  run_test (test_parse_tree_2_aig_vector_integer_2);
  run_test (test_parse_tree_2_aig_vector_integer_3);
  run_test (test_parse_tree_2_aig_vector_integer_4);
  run_test (test_parse_tree_2_aig_vector_integer_5);
  run_test (test_parse_tree_2_aig_vector_integer_random);
  run_test (test_parse_tree_2_aig_vector_not_1);
  run_test (test_parse_tree_2_aig_vector_not_2);
  run_test (test_parse_tree_2_aig_vector_not_3);
  run_test (test_parse_tree_2_aig_vector_not_4);
  run_test (test_parse_tree_2_aig_vector_not_5);
  run_test (test_parse_tree_2_aig_vector_not_random);
  run_test (test_parse_tree_2_aig_vector_comp_1);
  run_test (test_parse_tree_2_aig_vector_comp_2);
  run_test (test_parse_tree_2_aig_vector_comp_3);
  run_test (test_parse_tree_2_aig_vector_comp_4);
  run_test (test_parse_tree_2_aig_vector_comp_5);
  run_test (test_parse_tree_2_aig_vector_comp_random);
  run_test (test_parse_tree_2_aig_vector_unary_minus_1);
  run_test (test_parse_tree_2_aig_vector_unary_minus_2);
  run_test (test_parse_tree_2_aig_vector_unary_minus_3);
  run_test (test_parse_tree_2_aig_vector_unary_minus_4);
  run_test (test_parse_tree_2_aig_vector_unary_minus_5);
  run_test (test_parse_tree_2_aig_vector_unary_minus_random);
  run_test (test_parse_tree_2_aig_vector_and_1);
  run_test (test_parse_tree_2_aig_vector_and_2);
  run_test (test_parse_tree_2_aig_vector_and_3);
  run_test (test_parse_tree_2_aig_vector_and_4);
  run_test (test_parse_tree_2_aig_vector_and_5);
  run_test (test_parse_tree_2_aig_vector_and_random);
  run_test (test_parse_tree_2_aig_vector_or_1);
  run_test (test_parse_tree_2_aig_vector_or_2);
  run_test (test_parse_tree_2_aig_vector_or_3);
  run_test (test_parse_tree_2_aig_vector_or_4);
  run_test (test_parse_tree_2_aig_vector_or_5);
  run_test (test_parse_tree_2_aig_vector_or_random);
  run_test (test_parse_tree_2_aig_vector_imp_1);
  run_test (test_parse_tree_2_aig_vector_imp_2);
  run_test (test_parse_tree_2_aig_vector_imp_3);
  run_test (test_parse_tree_2_aig_vector_imp_4);
  run_test (test_parse_tree_2_aig_vector_imp_5);
  run_test (test_parse_tree_2_aig_vector_imp_random);
  run_test (test_parse_tree_2_aig_vector_dimp_1);
  run_test (test_parse_tree_2_aig_vector_dimp_2);
  run_test (test_parse_tree_2_aig_vector_dimp_3);
  run_test (test_parse_tree_2_aig_vector_dimp_4);
  run_test (test_parse_tree_2_aig_vector_dimp_5);
  run_test (test_parse_tree_2_aig_vector_dimp_random);
  run_test (test_parse_tree_2_aig_vector_band_1);
  run_test (test_parse_tree_2_aig_vector_band_2);
  run_test (test_parse_tree_2_aig_vector_band_3);
  run_test (test_parse_tree_2_aig_vector_band_4);
  run_test (test_parse_tree_2_aig_vector_band_5);
  run_test (test_parse_tree_2_aig_vector_band_random);
  run_test (test_parse_tree_2_aig_vector_bor_1);
  run_test (test_parse_tree_2_aig_vector_bor_2);
  run_test (test_parse_tree_2_aig_vector_bor_3);
  run_test (test_parse_tree_2_aig_vector_bor_4);
  run_test (test_parse_tree_2_aig_vector_bor_5);
  run_test (test_parse_tree_2_aig_vector_bor_random);
  run_test (test_parse_tree_2_aig_vector_bxor_1);
  run_test (test_parse_tree_2_aig_vector_bxor_2);
  run_test (test_parse_tree_2_aig_vector_bxor_3);
  run_test (test_parse_tree_2_aig_vector_bxor_4);
  run_test (test_parse_tree_2_aig_vector_bxor_5);
  run_test (test_parse_tree_2_aig_vector_bxor_random);
  run_test (test_parse_tree_2_aig_vector_plus_1);
  run_test (test_parse_tree_2_aig_vector_plus_2);
  run_test (test_parse_tree_2_aig_vector_plus_3);
  run_test (test_parse_tree_2_aig_vector_plus_4);
  run_test (test_parse_tree_2_aig_vector_plus_5);
  run_test (test_parse_tree_2_aig_vector_plus_random);
  run_test (test_parse_tree_2_aig_vector_binary_minus_1);
  run_test (test_parse_tree_2_aig_vector_binary_minus_2);
  run_test (test_parse_tree_2_aig_vector_binary_minus_3);
  run_test (test_parse_tree_2_aig_vector_binary_minus_4);
  run_test (test_parse_tree_2_aig_vector_binary_minus_5);
  run_test (test_parse_tree_2_aig_vector_binary_minus_random);
  run_test (test_parse_tree_2_aig_vector_eq_1);
  run_test (test_parse_tree_2_aig_vector_eq_2);
  run_test (test_parse_tree_2_aig_vector_eq_3);
  run_test (test_parse_tree_2_aig_vector_eq_4);
  run_test (test_parse_tree_2_aig_vector_eq_5);
  run_test (test_parse_tree_2_aig_vector_eq_random);
  run_test (test_parse_tree_2_aig_vector_neq_1);
  run_test (test_parse_tree_2_aig_vector_neq_2);
  run_test (test_parse_tree_2_aig_vector_neq_3);
  run_test (test_parse_tree_2_aig_vector_neq_4);
  run_test (test_parse_tree_2_aig_vector_neq_5);
  run_test (test_parse_tree_2_aig_vector_neq_random);
  run_test (test_parse_tree_2_aig_vector_lt_1);
  run_test (test_parse_tree_2_aig_vector_lt_2);
  run_test (test_parse_tree_2_aig_vector_lt_3);
  run_test (test_parse_tree_2_aig_vector_lt_4);
  run_test (test_parse_tree_2_aig_vector_lt_5);
  run_test (test_parse_tree_2_aig_vector_lt_random);
  run_test (test_parse_tree_2_aig_vector_lte_1);
  run_test (test_parse_tree_2_aig_vector_lte_2);
  run_test (test_parse_tree_2_aig_vector_lte_3);
  run_test (test_parse_tree_2_aig_vector_lte_4);
  run_test (test_parse_tree_2_aig_vector_lte_5);
  run_test (test_parse_tree_2_aig_vector_lte_random);
  run_test (test_parse_tree_2_aig_vector_gt_1);
  run_test (test_parse_tree_2_aig_vector_gt_2);
  run_test (test_parse_tree_2_aig_vector_gt_3);
  run_test (test_parse_tree_2_aig_vector_gt_4);
  run_test (test_parse_tree_2_aig_vector_gt_5);
  run_test (test_parse_tree_2_aig_vector_gt_random);
  run_test (test_parse_tree_2_aig_vector_gte_1);
  run_test (test_parse_tree_2_aig_vector_gte_2);
  run_test (test_parse_tree_2_aig_vector_gte_3);
  run_test (test_parse_tree_2_aig_vector_gte_4);
  run_test (test_parse_tree_2_aig_vector_gte_5);
  run_test (test_parse_tree_2_aig_vector_gte_random);
  run_test (test_parse_tree_2_aig_vector_shiftl_1);
  run_test (test_parse_tree_2_aig_vector_shiftl_2);
  run_test (test_parse_tree_2_aig_vector_shiftl_3);
  run_test (test_parse_tree_2_aig_vector_shiftl_4);
  run_test (test_parse_tree_2_aig_vector_shiftl_5);
  run_test (test_parse_tree_2_aig_vector_shiftl_random);
  run_test (test_parse_tree_2_aig_vector_shiftr_1);
  run_test (test_parse_tree_2_aig_vector_shiftr_2);
  run_test (test_parse_tree_2_aig_vector_shiftr_3);
  run_test (test_parse_tree_2_aig_vector_shiftr_4);
  run_test (test_parse_tree_2_aig_vector_shiftr_5);
  run_test (test_parse_tree_2_aig_vector_shiftr_random);
  run_test (test_parse_tree_2_aig_vector_multiply_1);
  run_test (test_parse_tree_2_aig_vector_multiply_2);
  run_test (test_parse_tree_2_aig_vector_multiply_3);
  run_test (test_parse_tree_2_aig_vector_multiply_4);
  run_test (test_parse_tree_2_aig_vector_multiply_5);
  run_test (test_parse_tree_2_aig_vector_multiply_random);
  run_test (test_parse_tree_2_aig_vector_divide_1);
  run_test (test_parse_tree_2_aig_vector_divide_2);
  run_test (test_parse_tree_2_aig_vector_divide_3);
  run_test (test_parse_tree_2_aig_vector_divide_4);
  run_test (test_parse_tree_2_aig_vector_divide_5);
  run_test (test_parse_tree_2_aig_vector_divide_random);
  run_test (test_parse_tree_2_aig_vector_modulo_1);
  run_test (test_parse_tree_2_aig_vector_modulo_2);
  run_test (test_parse_tree_2_aig_vector_modulo_3);
  run_test (test_parse_tree_2_aig_vector_modulo_4);
  run_test (test_parse_tree_2_aig_vector_modulo_5);
  run_test (test_parse_tree_2_aig_vector_modulo_random);
  run_test (test_parse_tree_2_aig_vector_if_then_else_1);
  run_test (test_parse_tree_2_aig_vector_if_then_else_2);
  run_test (test_parse_tree_2_aig_vector_if_then_else_3);
  run_test (test_parse_tree_2_aig_vector_if_then_else_4);
  run_test (test_parse_tree_2_aig_vector_if_then_else_5);
  run_test (test_parse_tree_2_aig_vector_if_then_else_random);
  run_test (test_parse_tree_2_aig_vector_bool_var);
  run_test (test_parse_tree_2_aig_vector_32bit_var);
}
