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
#include <limits.h>
#include "parser_test.h"
#include "test_logging.h"
#include "../token.h"
#include "../memory_management.h"
#include "../error_management.h"
#include "../scanner.h"
#include "../parser.h"
#include "../parse_tree.h"

void
test_create_delete_parser ()
{
  FILE *input = fopen ("input/basic1.c32sat", "r");
  Scanner *scanner = NULL;
  Parser *parser = NULL;
  init_error_management (stderr);
  init_memory_management ();
  scanner = create_scanner (input);
  parser = create_parser (scanner);
  assert (parser->scanner == scanner);
  assert (parser->la == NULL);
  delete_parser (parser);
  delete_scanner (scanner);
  finalise_memory_management ();
  fclose (input);
}

void
test_parse_basic1 ()
{
  FILE *input = fopen ("input/basic1.c32sat", "r");
  ParseTree *tree = NULL;
  Scanner *scanner = NULL;
  Parser *parser = NULL;
  init_error_management (stderr);
  init_memory_management ();
  scanner = create_scanner (input);
  parser = create_parser (scanner);
  tree = parse (parser);
  assert (tree->root->kind == ptn_ident
          && strcmp (tree->root->core.str, "x") == 0);
  delete_parse_tree (tree);
  delete_parser (parser);
  delete_scanner (scanner);
  finalise_memory_management ();
  fclose (input);
}

void
test_parse_basic2 ()
{
  FILE *input = fopen ("input/basic2.c32sat", "r");
  ParseTree *tree = NULL;
  Scanner *scanner = NULL;
  Parser *parser = NULL;
  init_error_management (stderr);
  init_memory_management ();
  scanner = create_scanner (input);
  parser = create_parser (scanner);
  tree = parse (parser);
  assert (tree->root->kind == ptn_integer && tree->root->core.val == 3);
  delete_parse_tree (tree);
  delete_parser (parser);
  delete_scanner (scanner);
  finalise_memory_management ();
  fclose (input);
}

void
test_parse_basic3 ()
{
  FILE *input = fopen ("input/basic3.c32sat", "r");
  ParseTree *tree = NULL;
  Scanner *scanner = NULL;
  Parser *parser = NULL;
  init_error_management (stderr);
  init_memory_management ();
  scanner = create_scanner (input);
  parser = create_parser (scanner);
  tree = parse (parser);
  assert (tree->root->kind == ptn_integer && tree->root->core.val == 3);
  delete_parse_tree (tree);
  delete_parser (parser);
  delete_scanner (scanner);
  finalise_memory_management ();
  fclose (input);
}

void
test_parse_basic4 ()
{
  FILE *input = fopen ("input/basic4.c32sat", "r");
  ParseTree *tree = NULL;
  Scanner *scanner = NULL;
  Parser *parser = NULL;
  init_error_management (stderr);
  init_memory_management ();
  scanner = create_scanner (input);
  parser = create_parser (scanner);
  tree = parse (parser);
  assert (tree->root->kind == ptn_integer && tree->root->core.val == INT_MAX);
  delete_parse_tree (tree);
  delete_parser (parser);
  delete_scanner (scanner);
  finalise_memory_management ();
  fclose (input);
}

void
test_parse_basic5 ()
{
  FILE *input = fopen ("input/basic5.c32sat", "r");
  ParseTree *tree = NULL;
  Scanner *scanner = NULL;
  Parser *parser = NULL;
  init_error_management (stderr);
  init_memory_management ();
  scanner = create_scanner (input);
  parser = create_parser (scanner);
  tree = parse (parser);
  assert (tree->root->kind == ptn_binary_minus);
  assert (tree->root->core.children[0]->kind == ptn_unary_minus);
  assert (tree->root->core.children[0]->core.children[0]->kind == ptn_integer);
  assert (tree->root->core.children[0]->core.children[0]->core.val == INT_MAX);
  assert (tree->root->core.children[1]->kind == ptn_integer);
  assert (tree->root->core.children[1]->core.val == 1);
  delete_parse_tree (tree);
  delete_parser (parser);
  delete_scanner (scanner);
  finalise_memory_management ();
  fclose (input);
}

void
test_parse_neg ()
{
  FILE *input = fopen ("input/neg.c32sat", "r");
  ParseTree *tree = NULL;
  Scanner *scanner = NULL;
  Parser *parser = NULL;
  init_error_management (stderr);
  init_memory_management ();
  scanner = create_scanner (input);
  parser = create_parser (scanner);
  tree = parse (parser);
  assert (tree->root->kind == ptn_unary_minus);
  assert (tree->root->core.children[0]->kind == ptn_not);
  assert (tree->root->core.children[0]->core.children[0]->kind ==
          ptn_unary_minus);
  assert (tree->root->core.children[0]->core.children[0]->core.children[0]->
          kind == ptn_comp);
  assert (tree->root->core.children[0]->core.children[0]->core.children[0]->
          core.children[0]->kind == ptn_ident
          && strcmp (tree->root->core.children[0]->core.children[0]->core.
                     children[0]->core.children[0]->core.str, "x") == 0);
  delete_parse_tree (tree);
  delete_parser (parser);
  delete_scanner (scanner);
  finalise_memory_management ();
  fclose (input);
}

void
test_parse_mul ()
{
  FILE *input = fopen ("input/mul.c32sat", "r");
  ParseTree *tree = NULL;
  Scanner *scanner = NULL;
  Parser *parser = NULL;
  init_error_management (stderr);
  init_memory_management ();
  scanner = create_scanner (input);
  parser = create_parser (scanner);
  tree = parse (parser);
  assert (tree->root->kind == ptn_mod);
  assert (tree->root->core.children[0]->kind == ptn_div);
  assert (tree->root->core.children[0]->core.children[0]->kind == ptn_mult);
  assert (tree->root->core.children[1]->kind == ptn_integer
          && tree->root->core.children[1]->core.val == 2);
  assert (tree->root->core.children[0]->core.children[1]->kind == ptn_integer
          && tree->root->core.children[0]->core.children[1]->core.val == 3);
  assert (tree->root->core.children[0]->core.children[0]->core.children[1]->
          kind == ptn_integer
          && tree->root->core.children[0]->core.children[0]->core.
          children[1]->core.val == 2);
  assert (tree->root->core.children[0]->core.children[0]->core.children[0]->
          kind == ptn_ident
          && strcmp (tree->root->core.children[0]->core.children[0]->core.
                     children[0]->core.str, "x") == 0);
  delete_parse_tree (tree);
  delete_parser (parser);
  delete_scanner (scanner);
  finalise_memory_management ();
  fclose (input);
}

void
test_parse_add ()
{
  FILE *input = fopen ("input/add.c32sat", "r");
  ParseTree *tree = NULL;
  Scanner *scanner = NULL;
  Parser *parser = NULL;
  init_error_management (stderr);
  init_memory_management ();
  scanner = create_scanner (input);
  parser = create_parser (scanner);
  tree = parse (parser);
  assert (tree->root->kind == ptn_plus);
  assert (tree->root->core.children[0]->kind == ptn_binary_minus);
  assert (tree->root->core.children[0]->core.children[0]->kind == ptn_plus);
  assert (tree->root->core.children[1]->kind == ptn_integer
          && tree->root->core.children[1]->core.val == 2);
  assert (tree->root->core.children[0]->core.children[1]->kind == ptn_integer
          && tree->root->core.children[0]->core.children[1]->core.val == 3);
  assert (tree->root->core.children[0]->core.children[0]->core.children[1]->
          kind == ptn_integer
          && tree->root->core.children[0]->core.children[0]->core.
          children[1]->core.val == 2);
  assert (tree->root->core.children[0]->core.children[0]->core.children[0]->
          kind == ptn_ident
          && strcmp (tree->root->core.children[0]->core.children[0]->core.
                     children[0]->core.str, "x") == 0);
  delete_parse_tree (tree);
  delete_parser (parser);
  delete_scanner (scanner);
  finalise_memory_management ();
  fclose (input);
}

void
test_parse_shift ()
{
  FILE *input = fopen ("input/shift.c32sat", "r");
  ParseTree *tree = NULL;
  Scanner *scanner = NULL;
  Parser *parser = NULL;
  init_error_management (stderr);
  init_memory_management ();
  scanner = create_scanner (input);
  parser = create_parser (scanner);
  tree = parse (parser);
  assert (tree->root->kind == ptn_shiftr);
  assert (tree->root->core.children[0]->kind == ptn_shiftl);
  assert (tree->root->core.children[0]->core.children[0]->kind == ptn_shiftr);
  assert (tree->root->core.children[1]->kind == ptn_integer
          && tree->root->core.children[1]->core.val == 2);
  assert (tree->root->core.children[0]->core.children[1]->kind == ptn_integer
          && tree->root->core.children[0]->core.children[1]->core.val == 3);
  assert (tree->root->core.children[0]->core.children[0]->core.children[1]->
          kind == ptn_integer
          && tree->root->core.children[0]->core.children[0]->core.
          children[1]->core.val == 2);
  assert (tree->root->core.children[0]->core.children[0]->core.children[0]->
          kind == ptn_ident
          && strcmp (tree->root->core.children[0]->core.children[0]->core.
                     children[0]->core.str, "x") == 0);
  delete_parse_tree (tree);
  delete_parser (parser);
  delete_scanner (scanner);
  finalise_memory_management ();
  fclose (input);
}

void
test_parse_rel ()
{
  FILE *input = fopen ("input/rel.c32sat", "r");
  ParseTree *tree = NULL;
  Scanner *scanner = NULL;
  Parser *parser = NULL;
  init_error_management (stderr);
  init_memory_management ();
  scanner = create_scanner (input);
  parser = create_parser (scanner);
  tree = parse (parser);
  assert (tree->root->kind == ptn_gt);
  assert (tree->root->core.children[0]->kind == ptn_lte);
  assert (tree->root->core.children[0]->core.children[0]->kind == ptn_gte);
  assert (tree->root->core.children[0]->core.children[0]->core.children[0]->
          kind == ptn_lt);
  assert (tree->root->core.children[1]->kind == ptn_integer
          && tree->root->core.children[1]->core.val == 0);
  assert (tree->root->core.children[0]->core.children[1]->kind == ptn_integer
          && tree->root->core.children[0]->core.children[1]->core.val == 1);
  assert (tree->root->core.children[0]->core.children[0]->core.children[1]->
          kind == ptn_integer
          && tree->root->core.children[0]->core.children[0]->core.
          children[1]->core.val == 0);
  assert (tree->root->core.children[0]->core.children[0]->core.children[0]->
          core.children[1]->kind == ptn_integer
          && tree->root->core.children[0]->core.children[0]->core.
          children[0]->core.children[1]->core.val == 4);
  assert (tree->root->core.children[0]->core.children[0]->core.children[0]->
          core.children[0]->kind == ptn_integer
          && tree->root->core.children[0]->core.children[0]->core.
          children[0]->core.children[0]->core.val == 3);
  delete_parse_tree (tree);
  delete_parser (parser);
  delete_scanner (scanner);
  finalise_memory_management ();
  fclose (input);
}

void
test_parse_eq ()
{
  FILE *input = fopen ("input/eq.c32sat", "r");
  ParseTree *tree = NULL;
  Scanner *scanner = NULL;
  Parser *parser = NULL;
  init_error_management (stderr);
  init_memory_management ();
  scanner = create_scanner (input);
  parser = create_parser (scanner);
  tree = parse (parser);
  assert (tree->root->kind == ptn_eq);
  assert (tree->root->core.children[1]->kind == ptn_integer
          && tree->root->core.children[1]->core.val == 4);
  assert (tree->root->core.children[0]->kind == ptn_neq);
  assert (tree->root->core.children[0]->core.children[0]->kind == ptn_eq);
  assert (tree->root->core.children[0]->core.children[1]->kind == ptn_integer
          && tree->root->core.children[0]->core.children[1]->core.val == 3);
  assert (tree->root->core.children[0]->core.children[0]->core.children[0]->
          kind == ptn_ident
          && strcmp (tree->root->core.children[0]->core.children[0]->core.
                     children[0]->core.str, "x") == 0);
  assert (tree->root->core.children[0]->core.children[0]->core.children[1]->
          kind == ptn_integer
          && tree->root->core.children[0]->core.children[0]->core.
          children[1]->core.val == 2);
  delete_parse_tree (tree);
  delete_parser (parser);
  delete_scanner (scanner);
  finalise_memory_management ();
  fclose (input);
}

void
test_parse_b_and ()
{
  FILE *input = fopen ("input/b_and.c32sat", "r");
  ParseTree *tree = NULL;
  Scanner *scanner = NULL;
  Parser *parser = NULL;
  init_error_management (stderr);
  init_memory_management ();
  scanner = create_scanner (input);
  parser = create_parser (scanner);
  tree = parse (parser);
  assert (tree->root->kind == ptn_band);
  assert (tree->root->core.children[1]->kind == ptn_integer
          && tree->root->core.children[1]->core.val == 4);
  assert (tree->root->core.children[0]->kind == ptn_band);
  assert (tree->root->core.children[0]->core.children[0]->kind == ptn_band);
  assert (tree->root->core.children[0]->core.children[1]->kind == ptn_integer
          && tree->root->core.children[0]->core.children[1]->core.val == 3);
  assert (tree->root->core.children[0]->core.children[0]->core.children[0]->
          kind == ptn_ident
          && strcmp (tree->root->core.children[0]->core.children[0]->core.
                     children[0]->core.str, "x") == 0);
  assert (tree->root->core.children[0]->core.children[0]->core.children[1]->
          kind == ptn_integer
          && tree->root->core.children[0]->core.children[0]->core.
          children[1]->core.val == 2);
  delete_parse_tree (tree);
  delete_parser (parser);
  delete_scanner (scanner);
  finalise_memory_management ();
  fclose (input);
}

void
test_parse_b_xor ()
{
  FILE *input = fopen ("input/b_xor.c32sat", "r");
  ParseTree *tree = NULL;
  Scanner *scanner = NULL;
  Parser *parser = NULL;
  init_error_management (stderr);
  init_memory_management ();
  scanner = create_scanner (input);
  parser = create_parser (scanner);
  tree = parse (parser);
  assert (tree->root->kind == ptn_bxor);
  assert (tree->root->core.children[1]->kind == ptn_integer
          && tree->root->core.children[1]->core.val == 4);
  assert (tree->root->core.children[0]->kind == ptn_bxor);
  assert (tree->root->core.children[0]->core.children[0]->kind == ptn_bxor);
  assert (tree->root->core.children[0]->core.children[1]->kind == ptn_integer
          && tree->root->core.children[0]->core.children[1]->core.val == 3);
  assert (tree->root->core.children[0]->core.children[0]->core.children[0]->
          kind == ptn_ident
          && strcmp (tree->root->core.children[0]->core.children[0]->core.
                     children[0]->core.str, "x") == 0);
  assert (tree->root->core.children[0]->core.children[0]->core.children[1]->
          kind == ptn_integer
          && tree->root->core.children[0]->core.children[0]->core.
          children[1]->core.val == 2);
  delete_parse_tree (tree);
  delete_parser (parser);
  delete_scanner (scanner);
  finalise_memory_management ();
  fclose (input);
}

void
test_parse_b_or ()
{
  FILE *input = fopen ("input/b_or.c32sat", "r");
  ParseTree *tree = NULL;
  Scanner *scanner = NULL;
  Parser *parser = NULL;
  init_error_management (stderr);
  init_memory_management ();
  scanner = create_scanner (input);
  parser = create_parser (scanner);
  tree = parse (parser);
  assert (tree->root->kind == ptn_bor);
  assert (tree->root->core.children[1]->kind == ptn_integer
          && tree->root->core.children[1]->core.val == 4);
  assert (tree->root->core.children[0]->kind == ptn_bor);
  assert (tree->root->core.children[0]->core.children[0]->kind == ptn_bor);
  assert (tree->root->core.children[0]->core.children[1]->kind == ptn_integer
          && tree->root->core.children[0]->core.children[1]->core.val == 3);
  assert (tree->root->core.children[0]->core.children[0]->core.children[0]->
          kind == ptn_ident
          && strcmp (tree->root->core.children[0]->core.children[0]->core.
                     children[0]->core.str, "x") == 0);
  assert (tree->root->core.children[0]->core.children[0]->core.children[1]->
          kind == ptn_integer
          && tree->root->core.children[0]->core.children[0]->core.
          children[1]->core.val == 2);
  delete_parse_tree (tree);
  delete_parser (parser);
  delete_scanner (scanner);
  finalise_memory_management ();
  fclose (input);
}

void
test_parse_and ()
{
  FILE *input = fopen ("input/and.c32sat", "r");
  ParseTree *tree = NULL;
  Scanner *scanner = NULL;
  Parser *parser = NULL;
  init_error_management (stderr);
  init_memory_management ();
  scanner = create_scanner (input);
  parser = create_parser (scanner);
  tree = parse (parser);
  assert (tree->root->kind == ptn_and);
  assert (tree->root->core.children[1]->kind == ptn_integer
          && tree->root->core.children[1]->core.val == 4);
  assert (tree->root->core.children[0]->kind == ptn_and);
  assert (tree->root->core.children[0]->core.children[0]->kind == ptn_and);
  assert (tree->root->core.children[0]->core.children[1]->kind == ptn_integer
          && tree->root->core.children[0]->core.children[1]->core.val == 3);
  assert (tree->root->core.children[0]->core.children[0]->core.children[0]->
          kind == ptn_ident
          && strcmp (tree->root->core.children[0]->core.children[0]->core.
                     children[0]->core.str, "x") == 0);
  assert (tree->root->core.children[0]->core.children[0]->core.children[1]->
          kind == ptn_integer
          && tree->root->core.children[0]->core.children[0]->core.
          children[1]->core.val == 2);
  delete_parse_tree (tree);
  delete_parser (parser);
  delete_scanner (scanner);
  finalise_memory_management ();
  fclose (input);
}

void
test_parse_or ()
{
  FILE *input = fopen ("input/or.c32sat", "r");
  ParseTree *tree = NULL;
  Scanner *scanner = NULL;
  Parser *parser = NULL;
  init_error_management (stderr);
  init_memory_management ();
  scanner = create_scanner (input);
  parser = create_parser (scanner);
  tree = parse (parser);
  assert (tree->root->kind == ptn_or);
  assert (tree->root->core.children[1]->kind == ptn_integer
          && tree->root->core.children[1]->core.val == 4);
  assert (tree->root->core.children[0]->kind == ptn_or);
  assert (tree->root->core.children[0]->core.children[0]->kind == ptn_or);
  assert (tree->root->core.children[0]->core.children[1]->kind == ptn_integer
          && tree->root->core.children[0]->core.children[1]->core.val == 3);
  assert (tree->root->core.children[0]->core.children[0]->core.children[0]->
          kind == ptn_ident
          && strcmp (tree->root->core.children[0]->core.children[0]->core.
                     children[0]->core.str, "x") == 0);
  assert (tree->root->core.children[0]->core.children[0]->core.children[1]->
          kind == ptn_integer
          && tree->root->core.children[0]->core.children[0]->core.
          children[1]->core.val == 2);
  delete_parse_tree (tree);
  delete_parser (parser);
  delete_scanner (scanner);
  finalise_memory_management ();
  fclose (input);
}

void
test_parse_imp ()
{
  FILE *input = fopen ("input/imp.c32sat", "r");
  ParseTree *tree = NULL;
  Scanner *scanner = NULL;
  Parser *parser = NULL;
  init_error_management (stderr);
  init_memory_management ();
  scanner = create_scanner (input);
  parser = create_parser (scanner);
  tree = parse (parser);
  assert (tree->root->kind == ptn_dimp);
  assert (tree->root->core.children[1]->kind == ptn_integer
          && tree->root->core.children[1]->core.val == 0);
  assert (tree->root->core.children[0]->kind == ptn_imp);
  assert (tree->root->core.children[0]->core.children[0]->kind == ptn_imp);
  assert (tree->root->core.children[0]->core.children[1]->kind == ptn_integer
          && tree->root->core.children[0]->core.children[1]->core.val == 5);
  assert (tree->root->core.children[0]->core.children[0]->core.children[0]->
          kind == ptn_ident
          && strcmp (tree->root->core.children[0]->core.children[0]->core.
                     children[0]->core.str, "y") == 0);
  assert (tree->root->core.children[0]->core.children[0]->core.children[1]->
          kind == ptn_integer
          && tree->root->core.children[0]->core.children[0]->core.
          children[1]->core.val == 3);
  delete_parse_tree (tree);
  delete_parser (parser);
  delete_scanner (scanner);
  finalise_memory_management ();
  fclose (input);
}

void
test_parse_ite ()
{
  FILE *input = fopen ("input/ite.c32sat", "r");
  ParseTree *tree = NULL;
  Scanner *scanner = NULL;
  Parser *parser = NULL;
  init_error_management (stderr);
  init_memory_management ();
  scanner = create_scanner (input);
  parser = create_parser (scanner);
  tree = parse (parser);
  assert (tree->root->kind == ptn_qm);
  assert (tree->root->core.children[0]->kind == ptn_eq);
  assert (tree->root->core.children[0]->core.children[0]->kind == ptn_ident
          && strcmp (tree->root->core.children[0]->core.children[0]->core.str,
                     "x") == 0);
  assert (tree->root->core.children[0]->core.children[1]->kind == ptn_integer
          && tree->root->core.children[0]->core.children[1]->core.val == 3);
  assert (tree->root->core.children[1]->kind == ptn_eq);
  assert (tree->root->core.children[1]->core.children[0]->kind == ptn_ident
          && strcmp (tree->root->core.children[1]->core.children[0]->core.str,
                     "y") == 0);
  assert (tree->root->core.children[1]->core.children[1]->kind == ptn_integer
          && tree->root->core.children[1]->core.children[1]->core.val == 1);
  assert (tree->root->core.children[2]->kind == ptn_eq);
  assert (tree->root->core.children[2]->core.children[0]->kind == ptn_ident
          && strcmp (tree->root->core.children[2]->core.children[0]->core.str,
                     "y") == 0);
  assert (tree->root->core.children[2]->core.children[1]->kind == ptn_integer
          && tree->root->core.children[2]->core.children[1]->core.val == 0);
  delete_parse_tree (tree);
  delete_parser (parser);
  delete_scanner (scanner);
  finalise_memory_management ();
  fclose (input);
}

void
test_parse_formula1 ()
{
  FILE *input = fopen ("input/formula1.c32sat", "r");
  ParseTree *tree = NULL;
  ParseTreeNode *impl = NULL;
  ParseTreeNode *and = NULL;
  ParseTreeNode *eq1 = NULL;
  ParseTreeNode *eq2 = NULL;
  ParseTreeNode *eq3 = NULL;
  ParseTreeNode *add = NULL;
  Scanner *scanner = NULL;
  Parser *parser = NULL;
  init_error_management (stderr);
  init_memory_management ();
  scanner = create_scanner (input);
  parser = create_parser (scanner);
  tree = parse (parser);
  impl = tree->root;
  assert (impl->kind == ptn_imp);
  and = impl->core.children[0];
  assert (and->kind == ptn_and);
  eq1 = and->core.children[0];
  assert (eq1->kind == ptn_eq);
  eq2 = and->core.children[1];
  assert (eq2->kind == ptn_eq);
  eq3 = impl->core.children[1];
  assert (eq3->kind == ptn_eq);
  add = eq3->core.children[1];
  assert (add->kind == ptn_plus);
  assert (eq1->core.children[0]->kind == ptn_ident
          && strcmp (eq1->core.children[0]->core.str, "x") == 0);
  assert (eq1->core.children[1]->kind == ptn_integer
          && eq1->core.children[1]->core.val == 2);
  assert (eq2->core.children[0]->kind == ptn_ident
          && strcmp (eq2->core.children[0]->core.str, "y") == 0);
  assert (eq2->core.children[1]->kind == ptn_integer
          && eq2->core.children[1]->core.val == 3);
  assert (eq3->core.children[0]->kind == ptn_ident
          && strcmp (eq3->core.children[0]->core.str, "y") == 0);
  assert (add->core.children[0]->kind == ptn_ident
          && strcmp (add->core.children[0]->core.str, "x") == 0);
  assert (add->core.children[1]->kind == ptn_integer
          && add->core.children[1]->core.val == 1);
  delete_parse_tree (tree);
  delete_parser (parser);
  delete_scanner (scanner);
  finalise_memory_management ();
  fclose (input);
}

void
test_parse_formula2 ()
{
  FILE *input = fopen ("input/formula2.c32sat", "r");
  ParseTree *tree = NULL;
  ParseTreeNode *impl = NULL;
  ParseTreeNode *and = NULL;
  ParseTreeNode *gt1 = NULL;
  ParseTreeNode *gt2 = NULL;
  ParseTreeNode *gt3 = NULL;
  Scanner *scanner = NULL;
  Parser *parser = NULL;
  init_error_management (stderr);
  init_memory_management ();
  scanner = create_scanner (input);
  parser = create_parser (scanner);
  tree = parse (parser);
  impl = tree->root;
  assert (impl->kind == ptn_imp);
  and = impl->core.children[0];
  assert (and->kind == ptn_and);
  gt1 = and->core.children[0];
  assert (gt1->kind == ptn_gt);
  gt2 = and->core.children[1];
  assert (gt2->kind == ptn_gt);
  gt3 = impl->core.children[1];
  assert (gt3->kind == ptn_gt);
  assert (gt1->core.children[0]->kind == ptn_ident
          && strcmp (gt1->core.children[0]->core.str, "x") == 0);
  assert (gt1->core.children[1]->kind == ptn_ident
          && strcmp (gt1->core.children[1]->core.str, "y") == 0);
  assert (gt2->core.children[0]->kind == ptn_ident
          && strcmp (gt2->core.children[0]->core.str, "y") == 0);
  assert (gt2->core.children[1]->kind == ptn_ident
          && strcmp (gt2->core.children[1]->core.str, "z") == 0);
  assert (gt3->core.children[0]->kind == ptn_ident
          && strcmp (gt3->core.children[0]->core.str, "x") == 0);
  assert (gt3->core.children[1]->kind == ptn_ident
          && strcmp (gt3->core.children[1]->core.str, "z") == 0);
  delete_parse_tree (tree);
  delete_parser (parser);
  delete_scanner (scanner);
  finalise_memory_management ();
  fclose (input);
}

void
test_parse_formula3 ()
{
  FILE *input = fopen ("input/formula3.c32sat", "r");
  ParseTree *tree = NULL;
  ParseTreeNode *eq = NULL;
  ParseTreeNode *plus = NULL;
  ParseTreeNode *mult = NULL;
  ParseTreeNode *div1 = NULL;
  ParseTreeNode *div2 = NULL;
  ParseTreeNode *unary_min = NULL;
  ParseTreeNode *binary_min = NULL;
  Scanner *scanner = NULL;
  Parser *parser = NULL;
  init_error_management (stderr);
  init_memory_management ();
  scanner = create_scanner (input);
  parser = create_parser (scanner);
  tree = parse (parser);
  eq = tree->root;
  assert (eq->kind == ptn_eq);
  mult = eq->core.children[0];
  assert (mult->kind == ptn_mult);
  plus = mult->core.children[0];
  assert (plus->kind == ptn_plus);
  div1 = plus->core.children[0];
  assert (div1->kind == ptn_div);
  unary_min = div1->core.children[0];
  assert (unary_min->kind == ptn_unary_minus);
  div2 = mult->core.children[1];
  assert (div2->kind == ptn_div);
  binary_min = div2->core.children[0];
  assert (binary_min->kind == ptn_binary_minus);
  assert (unary_min->core.children[0]->kind == ptn_integer
          && unary_min->core.children[0]->core.val == 4);
  assert (div1->core.children[1]->kind == ptn_integer
          && div1->core.children[1]->core.val == 2);
  assert (plus->core.children[1]->kind == ptn_integer
          && plus->core.children[1]->core.val == 3);
  assert (binary_min->core.children[0]->kind == ptn_integer
          && binary_min->core.children[0]->core.val == 9);
  assert (binary_min->core.children[1]->kind == ptn_integer
          && binary_min->core.children[1]->core.val == 3);
  assert (div2->core.children[1]->kind == ptn_integer
          && div2->core.children[1]->core.val == 2);
  assert (eq->core.children[1]->kind == ptn_integer
          && eq->core.children[1]->core.val == 3);
  delete_parse_tree (tree);
  delete_parser (parser);
  delete_scanner (scanner);
  finalise_memory_management ();
  fclose (input);
}

void
test_parse_formula4 ()
{
  FILE *input = fopen ("input/formula4.c32sat", "r");
  ParseTree *tree = NULL;
  ParseTreeNode *dimp = NULL;
  ParseTreeNode *eq1 = NULL;
  ParseTreeNode *eq2 = NULL;
  ParseTreeNode *and1 = NULL;
  ParseTreeNode *and2 = NULL;
  ParseTreeNode *not1 = NULL;
  ParseTreeNode *not2 = NULL;
  ParseTreeNode *not3 = NULL;
  ParseTreeNode *or = NULL;
  ParseTreeNode *band = NULL;
  ParseTreeNode *bor = NULL;
  ParseTreeNode *bxor = NULL;
  ParseTreeNode *comp = NULL;
  ParseTreeNode *mult = NULL;
  ParseTreeNode *div = NULL;
  ParseTreeNode *shiftl = NULL;
  ParseTreeNode *shiftr = NULL;
  ParseTreeNode *gte = NULL;
  ParseTreeNode *mod = NULL;
  ParseTreeNode *gt = NULL;
  ParseTreeNode *qm = NULL;
  Scanner *scanner = NULL;
  Parser *parser = NULL;
  init_error_management (stderr);
  init_memory_management ();
  scanner = create_scanner (input);
  parser = create_parser (scanner);
  tree = parse (parser);
  dimp = tree->root;
  assert (dimp->kind == ptn_dimp);
  and2 = dimp->core.children[0];
  assert (and2->kind == ptn_and);
  and1 = and2->core.children[0];
  assert (and1->kind == ptn_and);
  eq1 = and1->core.children[0];
  assert (eq1->kind == ptn_eq);
  eq2 = and1->core.children[1];
  assert (eq2->kind == ptn_eq);
  not1 = and2->core.children[1];
  assert (not1->kind == ptn_not);
  or = not1->core.children[0];
  assert (or->kind == ptn_or);
  band = or->core.children[0];
  assert (band->kind == ptn_band);
  not2 = band->core.children[0];
  assert (not2->kind == ptn_not);
  bor = or->core.children[1];
  assert (bor->kind == ptn_bor);
  not3 = bor->core.children[1];
  assert (not3->kind == ptn_not);
  bxor = not3->core.children[0];
  assert (bxor->kind == ptn_bxor);
  gte = dimp->core.children[1];
  assert (gte->kind == ptn_gte);
  mult = gte->core.children[0];
  assert (mult->kind == ptn_mult);
  comp = mult->core.children[0];
  assert (comp->kind == ptn_comp);
  shiftr = mult->core.children[1];
  assert (shiftr->kind == ptn_shiftr);
  div = shiftr->core.children[1];
  assert (div->kind == ptn_div);
  shiftl = div->core.children[1];
  assert (shiftl->kind == ptn_shiftl);
  mod = gte->core.children[1];
  assert (mod->kind == ptn_mod);
  qm = mod->core.children[1];
  assert (qm->kind == ptn_qm);
  gt = qm->core.children[0];
  assert (gt->kind == ptn_gt);
  assert (eq1->core.children[0]->kind == ptn_ident
          && strcmp (eq1->core.children[0]->core.str, "x") == 0);
  assert (eq1->core.children[1]->kind == ptn_integer
          && eq1->core.children[1]->core.val == 0);
  assert (eq2->core.children[0]->kind == ptn_ident
          && strcmp (eq2->core.children[0]->core.str, "y") == 0);
  assert (eq2->core.children[1]->kind == ptn_integer
          && eq2->core.children[1]->core.val == 1);
  assert (not2->core.children[0]->kind == ptn_ident
          && strcmp (not2->core.children[0]->core.str, "x") == 0);
  assert (band->core.children[1]->kind == ptn_ident
          && strcmp (band->core.children[1]->core.str, "x") == 0);
  assert (bor->core.children[0]->kind == ptn_ident
          && strcmp (bor->core.children[0]->core.str, "y") == 0);
  assert (bxor->core.children[0]->kind == ptn_ident
          && strcmp (bxor->core.children[0]->core.str, "y") == 0);
  assert (bxor->core.children[1]->kind == ptn_ident
          && strcmp (bxor->core.children[1]->core.str, "x") == 0);
  assert (comp->core.children[0]->kind == ptn_ident
          && strcmp (comp->core.children[0]->core.str, "y") == 0);
  assert (shiftr->core.children[0]->kind == ptn_ident
          && strcmp (shiftr->core.children[0]->core.str, "x") == 0);
  assert (div->core.children[0]->kind == ptn_integer
          && div->core.children[0]->core.val == 2);
  assert (shiftl->core.children[0]->kind == ptn_ident
          && strcmp (shiftl->core.children[0]->core.str, "y") == 0);
  assert (shiftl->core.children[1]->kind == ptn_integer
          && shiftl->core.children[1]->core.val == 3);
  assert (mod->core.children[0]->kind == ptn_integer
          && mod->core.children[0]->core.val == 3);
  assert (gt->core.children[0]->kind == ptn_ident
          && strcmp (gt->core.children[0]->core.str, "x") == 0);
  assert (gt->core.children[1]->kind == ptn_integer
          && gt->core.children[1]->core.val == 3);
  assert (qm->core.children[1]->kind == ptn_integer
          && qm->core.children[1]->core.val == 7);
  assert (qm->core.children[2]->kind == ptn_integer
          && qm->core.children[2]->core.val == 8);
  delete_parse_tree (tree);
  delete_parser (parser);
  delete_scanner (scanner);
  finalise_memory_management ();
  fclose (input);
}

void
test_parse_error (char *input, char *output)
{
  FILE *finput = fopen (input, "r");
  FILE *foutput = fopen (output, "w");
  ParseTree *tree = NULL;
  Scanner *scanner = NULL;
  Parser *parser = NULL;
  init_error_management (foutput);
  init_memory_management ();
  scanner = create_scanner (finput);
  parser = create_parser (scanner);
  tree = parse (parser);
  assert (tree->root == NULL);
  delete_parse_tree (tree);
  delete_parser (parser);
  delete_scanner (scanner);
  finalise_memory_management ();
  fclose (finput);
  fclose (foutput);
}

void
test_parse_error1 ()
{
  test_parse_error ("input/parser_error1.c32sat",
                    "output/parser_error1_output.txt");
}

void
test_parse_error2 ()
{
  test_parse_error ("input/parser_error2.c32sat",
                    "output/parser_error2_output.txt");
}

void
test_parse_error3 ()
{
  test_parse_error ("input/parser_error3.c32sat",
                    "output/parser_error3_output.txt");
}

void
test_parse_error4 ()
{
  test_parse_error ("input/parser_error4.c32sat",
                    "output/parser_error4_output.txt");
}

void
test_parse_error5 ()
{
  test_parse_error ("input/parser_error5.c32sat",
                    "output/parser_error5_output.txt");
}

void
test_parse_error6 ()
{
  test_parse_error ("input/parser_error6.c32sat",
                    "output/parser_error6_output.txt");
}

void
test_parse_error7 ()
{
  test_parse_error ("input/parser_error7.c32sat",
                    "output/parser_error7_output.txt");
}

void
test_parse_error8 ()
{
  test_parse_error ("input/parser_error8.c32sat",
                    "output/parser_error8_output.txt");
}

void
test_parse_error9 ()
{
  test_parse_error ("input/parser_error9.c32sat",
                    "output/parser_error9_output.txt");
}

void
test_parse_error10 ()
{
  test_parse_error ("input/parser_error10.c32sat",
                    "output/parser_error10_output.txt");
}

void
test_parse_error11 ()
{
  test_parse_error ("input/parser_error11.c32sat",
                    "output/parser_error11_output.txt");
}

void
test_parse_error12 ()
{
  test_parse_error ("input/parser_error12.c32sat",
                    "output/parser_error12_output.txt");
}

void
test_parse_error13 ()
{
  test_parse_error ("input/parser_error13.c32sat",
                    "output/parser_error13_output.txt");
}

void
test_parse_error14 ()
{
  test_parse_error ("input/parser_error14.c32sat",
                    "output/parser_error14_output.txt");
}

void
test_parse_error15 ()
{
  test_parse_error ("input/parser_error15.c32sat",
                    "output/parser_error15_output.txt");
}

void
test_parse_error16 ()
{
  test_parse_error ("input/parser_error16.c32sat",
                    "output/parser_error16_output.txt");
}

void
test_parse_error17 ()
{
  test_parse_error ("input/parser_error17.c32sat",
                    "output/parser_error17_output.txt");
}

void
test_parse_error18 ()
{
  test_parse_error ("input/parser_error18.c32sat",
                    "output/parser_error18_output.txt");
}

void
test_parse_error19 ()
{
  test_parse_error ("input/parser_error19.c32sat",
                    "output/parser_error19_output.txt");
}

void
test_parse_error20 ()
{
  test_parse_error ("input/parser_error20.c32sat",
                    "output/parser_error20_output.txt");
}

void
test_parse_error21 ()
{
  test_parse_error ("input/parser_error21.c32sat",
                    "output/parser_error21_output.txt");
}

void
test_parse_error22 ()
{
  test_parse_error ("input/parser_error22.c32sat",
                    "output/parser_error22_output.txt");
}

void
test_parse_error23 ()
{
  test_parse_error ("input/parser_error23.c32sat",
                    "output/parser_error23_output.txt");
}

void
test_parse_error24 ()
{
  test_parse_error ("input/parser_error24.c32sat",
                    "output/parser_error24_output.txt");
}

void
test_parse_error25 ()
{
  test_parse_error ("input/parser_error25.c32sat",
                    "output/parser_error25_output.txt");
}

void
test_parse_error26 ()
{
  test_parse_error ("input/parser_error26.c32sat",
                    "output/parser_error26_output.txt");
}

void
test_parse_error27 ()
{
  test_parse_error ("input/parser_error27.c32sat",
                    "output/parser_error27_output.txt");
}

void
test_parse_error28 ()
{
  test_parse_error ("input/parser_error28.c32sat",
                    "output/parser_error28_output.txt");
}

void
test_parse_error29 ()
{
  test_parse_error ("input/parser_error29.c32sat",
                    "output/parser_error29_output.txt");
}

void
test_parse_error30 ()
{
  test_parse_error ("input/parser_error30.c32sat",
                    "output/parser_error30_output.txt");
}

void
test_parse_error31 ()
{
  test_parse_error ("input/parser_error31.c32sat",
                    "output/parser_error31_output.txt");
}

void
test_parse_error32 ()
{
  test_parse_error ("input/parser_error32.c32sat",
                    "output/parser_error32_output.txt");
}

void
test_parse_error33 ()
{
  test_parse_error ("input/parser_error33.c32sat",
                    "output/parser_error33_output.txt");
}

void
run_parser_tests ()
{
  run_test (test_create_delete_parser);
  run_test (test_parse_basic1);
  run_test (test_parse_basic2);
  run_test (test_parse_basic3);
  run_test (test_parse_basic4);
  run_test (test_parse_basic5);
  run_test (test_parse_neg);
  run_test (test_parse_mul);
  run_test (test_parse_add);
  run_test (test_parse_shift);
  run_test (test_parse_rel);
  run_test (test_parse_eq);
  run_test (test_parse_b_and);
  run_test (test_parse_b_xor);
  run_test (test_parse_b_or);
  run_test (test_parse_and);
  run_test (test_parse_or);
  run_test (test_parse_imp);
  run_test (test_parse_ite);
  run_test (test_parse_formula1);
  run_test (test_parse_formula2);
  run_test (test_parse_formula3);
  run_test (test_parse_formula4);
  run_test (test_parse_error1);
  check_output ("output/parser_error1_expected.txt",
                "output/parser_error1_output.txt");
  run_test (test_parse_error2);
  check_output ("output/parser_error2_expected.txt",
                "output/parser_error2_output.txt");
  run_test (test_parse_error3);
  check_output ("output/parser_error3_expected.txt",
                "output/parser_error3_output.txt");
  run_test (test_parse_error4);
  check_output ("output/parser_error4_expected.txt",
                "output/parser_error4_output.txt");
  run_test (test_parse_error5);
  check_output ("output/parser_error5_expected.txt",
                "output/parser_error5_output.txt");
  run_test (test_parse_error6);
  check_output ("output/parser_error6_expected.txt",
                "output/parser_error6_output.txt");
  run_test (test_parse_error7);
  check_output ("output/parser_error7_expected.txt",
                "output/parser_error7_output.txt");
  run_test (test_parse_error8);
  check_output ("output/parser_error8_expected.txt",
                "output/parser_error8_output.txt");
  run_test (test_parse_error9);
  check_output ("output/parser_error9_expected.txt",
                "output/parser_error9_output.txt");
  run_test (test_parse_error10);
  check_output ("output/parser_error10_expected.txt",
                "output/parser_error10_output.txt");
  run_test (test_parse_error11);
  check_output ("output/parser_error11_expected.txt",
                "output/parser_error11_output.txt");
  run_test (test_parse_error12);
  check_output ("output/parser_error12_expected.txt",
                "output/parser_error12_output.txt");
  run_test (test_parse_error13);
  check_output ("output/parser_error13_expected.txt",
                "output/parser_error13_output.txt");
  run_test (test_parse_error14);
  check_output ("output/parser_error14_expected.txt",
                "output/parser_error14_output.txt");
  run_test (test_parse_error15);
  check_output ("output/parser_error15_expected.txt",
                "output/parser_error15_output.txt");
  run_test (test_parse_error16);
  check_output ("output/parser_error16_expected.txt",
                "output/parser_error16_output.txt");
  run_test (test_parse_error17);
  check_output ("output/parser_error17_expected.txt",
                "output/parser_error17_output.txt");
  run_test (test_parse_error18);
  check_output ("output/parser_error18_expected.txt",
                "output/parser_error18_output.txt");
  run_test (test_parse_error19);
  check_output ("output/parser_error19_expected.txt",
                "output/parser_error19_output.txt");
  run_test (test_parse_error20);
  check_output ("output/parser_error20_expected.txt",
                "output/parser_error20_output.txt");
  run_test (test_parse_error21);
  check_output ("output/parser_error21_expected.txt",
                "output/parser_error21_output.txt");
  run_test (test_parse_error22);
  check_output ("output/parser_error22_expected.txt",
                "output/parser_error22_output.txt");
  run_test (test_parse_error23);
  check_output ("output/parser_error23_expected.txt",
                "output/parser_error23_output.txt");
  run_test (test_parse_error24);
  check_output ("output/parser_error24_expected.txt",
                "output/parser_error24_output.txt");
  run_test (test_parse_error25);
  check_output ("output/parser_error25_expected.txt",
                "output/parser_error25_output.txt");
  run_test (test_parse_error26);
  check_output ("output/parser_error26_expected.txt",
                "output/parser_error26_output.txt");
  run_test (test_parse_error27);
  check_output ("output/parser_error27_expected.txt",
                "output/parser_error27_output.txt");
  run_test (test_parse_error28);
  check_output ("output/parser_error28_expected.txt",
                "output/parser_error28_output.txt");
  run_test (test_parse_error29);
  check_output ("output/parser_error29_expected.txt",
                "output/parser_error29_output.txt");
  run_test (test_parse_error30);
  check_output ("output/parser_error30_expected.txt",
                "output/parser_error30_output.txt");
  run_test (test_parse_error31);
  check_output ("output/parser_error31_expected.txt",
                "output/parser_error31_output.txt");
  run_test (test_parse_error32);
  check_output ("output/parser_error32_expected.txt",
                "output/parser_error32_output.txt");
  run_test (test_parse_error33);
  check_output ("output/parser_error33_expected.txt",
                "output/parser_error33_output.txt");
}
