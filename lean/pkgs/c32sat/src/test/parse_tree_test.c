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
#include <stdio.h>
#include <string.h>
#include "parse_tree_test.h"
#include "test_logging.h"
#include "../memory_management.h"
#include "../error_management.h"
#include "../scanner.h"
#include "../parser.h"
#include "../parse_tree.h"
#include "../hash_table.h"

void
test_create_delete_parse_tree_node ()
{
  ParseTreeNode *node = NULL;
  init_error_management (stderr);
  init_memory_management ();
  node = create_parse_tree_node (ptn_bxor);
  assert (node->kind == ptn_bxor);
  assert (node->core.children[0] == NULL);
  assert (node->core.children[1] == NULL);
  assert (node->core.children[2] == NULL);
  delete_parse_tree_node (node);
  finalise_memory_management ();
}

void
test_create_delete_parse_tree_ident_leaf ()
{
  ParseTreeNode *node = NULL;
  init_error_management (stderr);
  init_memory_management ();
  node = create_parse_tree_ident_leaf ("x");
  assert (node->kind == ptn_ident);
  assert (strcmp (node->core.str, "x") == 0);
  delete_parse_tree_node (node);
  finalise_memory_management ();
}

void
test_create_delete_parse_tree_integer_leaf ()
{
  ParseTreeNode *node = NULL;
  init_error_management (stderr);
  init_memory_management ();
  node = create_parse_tree_integer_leaf (16);
  assert (node->kind == ptn_integer);
  assert (node->core.val == 16);
  delete_parse_tree_node (node);
  finalise_memory_management ();
}

void
test_create_delete_parse_tree ()
{
  ParseTree *tree = NULL;
  ParseTreeNode *not1 = NULL;
  ParseTreeNode *not2 = NULL;
  ParseTreeNode *or = NULL;
  ParseTreeNode *integer = NULL;
  ParseTreeNode *ident = NULL;
  init_error_management (stderr);
  init_memory_management ();
  tree = create_parse_tree ();
  assert (tree->root == NULL);
  tree->root = create_parse_tree_node (ptn_not);
  not1 = create_parse_tree_node (ptn_not);
  not2 = create_parse_tree_node (ptn_not);
  or = create_parse_tree_node (ptn_or);
  integer = create_parse_tree_integer_leaf (39);
  ident = create_parse_tree_ident_leaf ("param34");
  tree->root->core.children[0] = not1;
  not1->core.children[0] = not2;
  not2->core.children[0] = or;
  or->core.children[0] = integer;
  or->core.children[1] = ident;
  delete_parse_tree (tree);
  finalise_memory_management ();
}

void
test_pretty_print_parse_tree (char *input, char *output)
{
  FILE *finput = fopen (input, "r");
  FILE *foutput = fopen (output, "w");
  ParseTree *tree = NULL;
  Scanner *scanner = NULL;
  Parser *parser = NULL;
  init_error_management (stderr);
  init_memory_management ();
  scanner = create_scanner (finput);
  parser = create_parser (scanner);
  tree = parse (parser);
  assert (tree->root != NULL);
  pretty_print_parse_tree (tree, foutput);
  delete_parse_tree (tree);
  delete_parser (parser);
  delete_scanner (scanner);
  finalise_memory_management ();
  fclose (finput);
  fclose (foutput);
}

void
test_pretty_print_parse_tree_formula1 ()
{
  test_pretty_print_parse_tree ("input/formula1.c32sat",
                                "output/pp_formula1_output.txt");
}

void
test_pretty_print_parse_tree_formula2 ()
{
  test_pretty_print_parse_tree ("input/formula2.c32sat",
                                "output/pp_formula2_output.txt");
}

void
test_pretty_print_parse_tree_formula3 ()
{
  test_pretty_print_parse_tree ("input/formula3.c32sat",
                                "output/pp_formula3_output.txt");
}

void
test_pretty_print_parse_tree_formula4 ()
{
  test_pretty_print_parse_tree ("input/formula4.c32sat",
                                "output/pp_formula4_output.txt");
}

void
test_pretty_print_parse_tree1 ()
{
  test_pretty_print_parse_tree ("input/pp1.c32sat", "output/pp1_output.txt");
}

void
test_pretty_print_parse_tree2 ()
{
  test_pretty_print_parse_tree ("input/pp2.c32sat", "output/pp2_output.txt");
}

void
test_pretty_print_parse_tree3 ()
{
  test_pretty_print_parse_tree ("input/pp3.c32sat", "output/pp3_output.txt");
}

void
test_pretty_print_parse_tree4 ()
{
  test_pretty_print_parse_tree ("input/pp4.c32sat", "output/pp4_output.txt");
}

void
test_pretty_print_parse_tree5 ()
{
  test_pretty_print_parse_tree ("input/pp5.c32sat", "output/pp5_output.txt");
}

void
test_pretty_print_parse_tree6 ()
{
  test_pretty_print_parse_tree ("input/pp6.c32sat", "output/pp6_output.txt");
}

void
test_pretty_print_parse_tree7 ()
{
  test_pretty_print_parse_tree ("input/pp7.c32sat", "output/pp7_output.txt");
}

void
run_parse_tree_tests ()
{
  run_test (test_create_delete_parse_tree_node);
  run_test (test_create_delete_parse_tree_ident_leaf);
  run_test (test_create_delete_parse_tree_integer_leaf);
  run_test (test_create_delete_parse_tree);
  run_test (test_pretty_print_parse_tree_formula1);
  check_output ("output/pp_formula1_expected.txt",
                "output/pp_formula1_output.txt");
  run_test (test_pretty_print_parse_tree_formula2);
  check_output ("output/pp_formula2_expected.txt",
                "output/pp_formula2_output.txt");
  run_test (test_pretty_print_parse_tree_formula3);
  check_output ("output/pp_formula3_expected.txt",
                "output/pp_formula3_output.txt");
  run_test (test_pretty_print_parse_tree_formula4);
  check_output ("output/pp_formula4_expected.txt",
                "output/pp_formula4_output.txt");
  run_test (test_pretty_print_parse_tree1);
  check_output ("output/pp1_expected.txt", "output/pp1_output.txt");
  run_test (test_pretty_print_parse_tree2);
  check_output ("output/pp2_expected.txt", "output/pp2_output.txt");
  run_test (test_pretty_print_parse_tree3);
  check_output ("output/pp3_expected.txt", "output/pp3_output.txt");
  run_test (test_pretty_print_parse_tree4);
  check_output ("output/pp4_expected.txt", "output/pp4_output.txt");
  run_test (test_pretty_print_parse_tree5);
  check_output ("output/pp5_expected.txt", "output/pp5_output.txt");
  run_test (test_pretty_print_parse_tree6);
  check_output ("output/pp6_expected.txt", "output/pp6_output.txt");
  run_test (test_pretty_print_parse_tree7);
  check_output ("output/pp7_expected.txt", "output/pp7_output.txt");
}
