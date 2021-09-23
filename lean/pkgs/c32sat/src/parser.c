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
#include "token.h"
#include "symbol.h"
#include "memory_management.h"
#include "error_management.h"
#include "scanner.h"
#include "parser.h"
#include "parse_tree.h"

/* Forward declarations */
static ParseTreeNode *parse_c32sat ();
static ParseTreeNode *parse_ite ();
static ParseTreeNode *parse_impl ();
static ParseTreeNode *parse_or ();
static ParseTreeNode *parse_and ();
static ParseTreeNode *parse_b_or ();
static ParseTreeNode *parse_b_xor ();
static ParseTreeNode *parse_b_and ();
static ParseTreeNode *parse_eq ();
static ParseTreeNode *parse_rel ();
static ParseTreeNode *parse_shift ();
static ParseTreeNode *parse_add ();
static ParseTreeNode *parse_mul ();
static ParseTreeNode *parse_neg ();
static ParseTreeNode *parse_basic ();

static Parser *g_parser;

static void
next_token ()
{
  Token *temp = g_parser->la;
  if (temp)
    {
      delete_token (temp);
    }
  g_parser->la = scan (g_parser->scanner);
}

static void
check (TokenKind expected)
{
  char *buffer = NULL;
  if (g_parser->la->kind != expected && !has_error_occured ())
    {
      switch (g_parser->la->kind)
        {
        case t_ident:
          error (e_parser_invalid_token, g_parser->la->line,
                 g_parser->la->col, 0, g_parser->la->str);
          break;
        case t_integer:
          buffer =
            (char *) malloc_c32sat (sizeof (char) *
                                    (g_parser->scanner->
                                     max_int_string_length + 1));
          sprintf (buffer, "%lld", g_parser->la->val);
          error (e_parser_invalid_token, g_parser->la->line,
                 g_parser->la->col, 0, buffer);
          free_c32sat (buffer,
                       sizeof (char) *
                       (g_parser->scanner->max_int_string_length + 1));
          break;
        default:
          error (e_parser_invalid_token, g_parser->la->line,
                 g_parser->la->col, 0, get_token_symbol (g_parser->la->kind));
          break;
        }
    }
  else
    {
      next_token ();
    }
}

static ParseTreeNode *
parse_c32sat ()
{
  ParseTreeNode *result = parse_ite ();
  if (result == NULL)
    {
      return NULL;
    }
  check (t_eof);
  if (has_error_occured ())
    {
      delete_parse_tree_node (result);
      return NULL;
    }
  return result;
}

static ParseTreeNode *
parse_ite ()
{
  ParseTreeNode *temp = NULL;
  ParseTreeNode *ite = parse_impl ();
  if (ite == NULL)
    {
      return NULL;
    }
  if (g_parser->la->kind == t_qm)
    {
      temp = ite;
      ite = create_parse_tree_node (ptn_qm);
      parse_tree_node_first_child (ite) = temp;
      next_token ();
      parse_tree_node_second_child (ite) = parse_impl ();
      if (parse_tree_node_second_child (ite) == NULL)
        {
          delete_parse_tree_node (ite);
          return NULL;
        }
      check (t_colon);
      if (has_error_occured ())
        {
          delete_parse_tree_node (ite);
          return NULL;
        }
      parse_tree_node_third_child (ite) = parse_impl ();
      if (parse_tree_node_third_child (ite) == NULL)
        {
          delete_parse_tree_node (ite);
          return NULL;
        }
    }
  return ite;
}

static ParseTreeNode *
parse_impl ()
{
  ParseTreeNode *temp = NULL;
  ParseTreeNode *result = parse_or ();
  if (result == NULL)
    {
      return NULL;
    }
  while (g_parser->la->kind == t_imp || g_parser->la->kind == t_dimp)
    {
      if (g_parser->la->kind == t_imp)
        {
          temp = create_parse_tree_node (ptn_imp);
        }
      else
        {
          temp = create_parse_tree_node (ptn_dimp);
        }
      next_token ();
      parse_tree_node_first_child (temp) = result;
      parse_tree_node_second_child (temp) = parse_or ();
      if (parse_tree_node_second_child (temp) == NULL)
        {
          delete_parse_tree_node (temp);
          return NULL;
        }
      result = temp;
    }
  return result;
}

static ParseTreeNode *
parse_or ()
{
  ParseTreeNode *temp = NULL;
  ParseTreeNode *result = parse_and ();
  if (result == NULL)
    {
      return NULL;
    }
  while (g_parser->la->kind == t_or)
    {
      temp = create_parse_tree_node (ptn_or);
      parse_tree_node_first_child (temp) = result;
      next_token ();
      parse_tree_node_second_child (temp) = parse_and ();
      if (parse_tree_node_second_child (temp) == NULL)
        {
          delete_parse_tree_node (temp);
          return NULL;
        }
      result = temp;
    }
  return result;
}

static ParseTreeNode *
parse_and ()
{
  ParseTreeNode *temp = NULL;
  ParseTreeNode *result = parse_b_or ();
  if (result == NULL)
    {
      return NULL;
    }
  while (g_parser->la->kind == t_and)
    {
      temp = create_parse_tree_node (ptn_and);
      parse_tree_node_first_child (temp) = result;
      next_token ();
      parse_tree_node_second_child (temp) = parse_b_or ();
      if (parse_tree_node_second_child (temp) == NULL)
        {
          delete_parse_tree_node (temp);
          return NULL;
        }
      result = temp;
    }
  return result;
}

static ParseTreeNode *
parse_b_or ()
{
  ParseTreeNode *temp = NULL;
  ParseTreeNode *result = parse_b_xor ();
  if (result == NULL)
    {
      return NULL;
    }
  while (g_parser->la->kind == t_bor)
    {
      temp = create_parse_tree_node (ptn_bor);
      parse_tree_node_first_child (temp) = result;
      next_token ();
      parse_tree_node_second_child (temp) = parse_b_xor ();
      if (parse_tree_node_second_child (temp) == NULL)
        {
          delete_parse_tree_node (temp);
          return NULL;
        }
      result = temp;
    }
  return result;
}

static ParseTreeNode *
parse_b_xor ()
{
  ParseTreeNode *temp = NULL;
  ParseTreeNode *result = parse_b_and ();
  if (result == NULL)
    {
      return NULL;
    }
  while (g_parser->la->kind == t_bxor)
    {
      temp = create_parse_tree_node (ptn_bxor);
      parse_tree_node_first_child (temp) = result;
      next_token ();
      parse_tree_node_second_child (temp) = parse_b_and ();
      if (parse_tree_node_second_child (temp) == NULL)
        {
          delete_parse_tree_node (temp);
          return NULL;
        }
      result = temp;
    }
  return result;
}

static ParseTreeNode *
parse_b_and ()
{
  ParseTreeNode *temp = NULL;
  ParseTreeNode *result = parse_eq ();
  if (result == NULL)
    {
      return NULL;
    }
  while (g_parser->la->kind == t_band)
    {
      temp = create_parse_tree_node (ptn_band);
      parse_tree_node_first_child (temp) = result;
      next_token ();
      parse_tree_node_second_child (temp) = parse_eq ();
      if (parse_tree_node_second_child (temp) == NULL)
        {
          delete_parse_tree_node (temp);
          return NULL;
        }
      result = temp;
    }
  return result;
}

static ParseTreeNode *
parse_eq ()
{
  ParseTreeNode *temp = NULL;
  ParseTreeNode *result = parse_rel ();
  if (result == NULL)
    {
      return NULL;
    }
  while (g_parser->la->kind == t_eq || g_parser->la->kind == t_neq)
    {
      if (g_parser->la->kind == t_eq)
        {
          temp = create_parse_tree_node (ptn_eq);
        }
      else
        {
          temp = create_parse_tree_node (ptn_neq);
        }
      next_token ();
      parse_tree_node_first_child (temp) = result;
      parse_tree_node_second_child (temp) = parse_rel ();
      if (parse_tree_node_second_child (temp) == NULL)
        {
          delete_parse_tree_node (temp);
          return NULL;
        }
      result = temp;
    }
  return result;
}

static ParseTreeNode *
parse_rel ()
{
  ParseTreeNode *temp = NULL;
  ParseTreeNode *result = parse_shift ();
  if (result == NULL)
    {
      return NULL;
    }
  while (g_parser->la->kind == t_lt || g_parser->la->kind == t_lte
         || g_parser->la->kind == t_gt || g_parser->la->kind == t_gte)
    {
      switch (g_parser->la->kind)
        {
        case t_lt:
          temp = create_parse_tree_node (ptn_lt);
          break;
        case t_lte:
          temp = create_parse_tree_node (ptn_lte);
          break;
        case t_gt:
          temp = create_parse_tree_node (ptn_gt);
          break;
        default:               /* t_gte */
          temp = create_parse_tree_node (ptn_gte);
          break;
        }
      next_token ();
      parse_tree_node_first_child (temp) = result;
      parse_tree_node_second_child (temp) = parse_shift ();
      if (parse_tree_node_second_child (temp) == NULL)
        {
          delete_parse_tree_node (temp);
          return NULL;
        }
      result = temp;
    }
  return result;
}

static ParseTreeNode *
parse_shift ()
{
  ParseTreeNode *temp = NULL;
  ParseTreeNode *result = parse_add ();
  if (result == NULL)
    {
      return NULL;
    }
  while (g_parser->la->kind == t_shiftl || g_parser->la->kind == t_shiftr)
    {
      if (g_parser->la->kind == t_shiftl)
        {
          temp = create_parse_tree_node (ptn_shiftl);
        }
      else
        {
          temp = create_parse_tree_node (ptn_shiftr);
        }
      next_token ();
      parse_tree_node_first_child (temp) = result;
      parse_tree_node_second_child (temp) = parse_add ();
      if (parse_tree_node_second_child (temp) == NULL)
        {
          delete_parse_tree_node (temp);
          return NULL;
        }
      result = temp;
    }
  return result;
}

static ParseTreeNode *
parse_add ()
{
  ParseTreeNode *temp = NULL;
  ParseTreeNode *result = parse_mul ();
  if (result == NULL)
    {
      return NULL;
    }
  while (g_parser->la->kind == t_plus || g_parser->la->kind == t_minus)
    {
      if (g_parser->la->kind == t_plus)
        {
          temp = create_parse_tree_node (ptn_plus);
        }
      else
        {
          temp = create_parse_tree_node (ptn_binary_minus);
        }
      next_token ();
      parse_tree_node_first_child (temp) = result;
      parse_tree_node_second_child (temp) = parse_mul ();
      if (parse_tree_node_second_child (temp) == NULL)
        {
          delete_parse_tree_node (temp);
          return NULL;
        }
      result = temp;
    }
  return result;
}

static ParseTreeNode *
parse_mul ()
{
  ParseTreeNode *temp = NULL;
  ParseTreeNode *result = parse_neg ();
  if (result == NULL)
    {
      return NULL;
    }
  while (g_parser->la->kind == t_mult || g_parser->la->kind == t_div
         || g_parser->la->kind == t_mod)
    {
      switch (g_parser->la->kind)
        {
        case t_mult:
          temp = create_parse_tree_node (ptn_mult);
          break;
        case t_div:
          temp = create_parse_tree_node (ptn_div);
          break;
        default:               /* t_mod */
          temp = create_parse_tree_node (ptn_mod);
          break;
        }
      next_token ();
      parse_tree_node_first_child (temp) = result;
      parse_tree_node_second_child (temp) = parse_neg ();
      if (parse_tree_node_second_child (temp) == NULL)
        {
          delete_parse_tree_node (temp);
          return NULL;
        }
      result = temp;
    }
  return result;
}

static ParseTreeNode *
parse_neg ()
{
  ParseTreeNode *result = NULL;
  ParseTreeNode *last = NULL;
  while (g_parser->la->kind == t_not || g_parser->la->kind == t_minus
         || g_parser->la->kind == t_comp)
    {
      switch (g_parser->la->kind)
        {
        case t_not:
          if (result == NULL)
            {
              result = create_parse_tree_node (ptn_not);
              last = result;
            }
          else
            {
              parse_tree_node_first_child (last) =
                create_parse_tree_node (ptn_not);
              last = parse_tree_node_first_child (last);
            }
          break;
        case t_minus:
          if (result == NULL)
            {
              result = create_parse_tree_node (ptn_unary_minus);
              last = result;
            }
          else
            {
              parse_tree_node_first_child (last) =
                create_parse_tree_node (ptn_unary_minus);
              last = parse_tree_node_first_child (last);
            }
          break;
        default:               /* t_comp */
          if (result == NULL)
            {
              result = create_parse_tree_node (ptn_comp);
              last = result;
            }
          else
            {
              parse_tree_node_first_child (last) =
                create_parse_tree_node (ptn_comp);
              last = parse_tree_node_first_child (last);
            }
          break;
        }
      next_token ();
    }
  if (result == NULL)
    {
      result = parse_basic ();
    }
  else
    {
      parse_tree_node_first_child (last) = parse_basic ();
      if (parse_tree_node_first_child (last) == NULL)
        {
          delete_parse_tree_node (result);
          result = NULL;
        }
    }
  return result;
}

static ParseTreeNode *
parse_basic ()
{
  ParseTreeNode *result = NULL;
  switch (g_parser->la->kind)
    {
    case t_ident:
      result = create_parse_tree_ident_leaf (g_parser->la->str);
      next_token ();
      break;
    case t_int_max:
      result = create_parse_tree_integer_leaf (g_parser->scanner->max_int_val);
      next_token ();
      break;
    case t_int_min:
      result = create_parse_tree_node(ptn_binary_minus);
      parse_tree_node_first_child (result) = create_parse_tree_node(ptn_unary_minus);
      parse_tree_node_first_child (parse_tree_node_first_child(result)) = 
         create_parse_tree_integer_leaf (g_parser->scanner->max_int_val);
      parse_tree_node_second_child (result) = create_parse_tree_integer_leaf(1);
      next_token ();
      break;
    case t_integer:
      result = create_parse_tree_integer_leaf (g_parser->la->val);
      next_token ();
      break;
    case t_lpar:
      next_token ();
      result = parse_ite ();
      check (t_rpar);
      if (has_error_occured ())
        {
          delete_parse_tree_node (result);
          return NULL;
        }
      break;
    default:
      if (!has_error_occured ())
        {
          error (e_parser_invalid_token, g_parser->la->line,
                 g_parser->la->col, 0, get_token_symbol (g_parser->la->kind));
        }
      break;
    }
  return result;
}

Parser *
create_parser (Scanner * scanner)
{
  Parser *parser = NULL;
  assert (scanner != NULL);
  parser = (Parser *) malloc_c32sat (sizeof (Parser));
  parser->scanner = scanner;
  parser->la = NULL;
  return parser;
}

void
delete_parser (Parser * parser)
{
  assert (parser != NULL);
  free_c32sat (parser, sizeof (Parser));
}

ParseTree *
parse (Parser * parser)
{
  ParseTree *tree = create_parse_tree ();
  assert (parser != NULL);
  g_parser = parser;
  next_token ();
  tree->root = parse_c32sat ();
  delete_token (g_parser->la);
  return tree;
}
