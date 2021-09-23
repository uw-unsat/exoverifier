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
#ifndef _PARSE_TREE_H_
#define _PARSE_TREE_H_

#include <stdio.h>
#include "token.h"

/** Represents the kind of a parse tree node. */
enum ParseTreeNodeKind
{
  /** Identifier */
  ptn_ident = 0,
  /** Integer */
  ptn_integer,
  /** Question mark */
  ptn_qm,
  /** Implication */
  ptn_imp,
  /** Double implication */
  ptn_dimp,
  /** Boolean or */
  ptn_or,
  /** Boolean and */
  ptn_and,
  /** Bitwise or */
  ptn_bor,
  /** Bitwise xor */
  ptn_bxor,
  /** Bitwise and */
  ptn_band,
  /** Equal */
  ptn_eq,
  /** Not equal */
  ptn_neq,
  /** Less than */
  ptn_lt,
  /** Less than or equal */
  ptn_lte,
  /** Greater than */
  ptn_gt,
  /** Greater than or equal */
  ptn_gte,
  /** Shift right */
  ptn_shiftr,
  /** Shift left */
  ptn_shiftl,
  /** Plus */
  ptn_plus,
  /** Binary minus */
  ptn_binary_minus,
  /** Unary minus */
  ptn_unary_minus,
  /** Multiplication */
  ptn_mult,
  /** Integer Division */
  ptn_div,
  /** Modulo */
  ptn_mod,
  /** Boolean not */
  ptn_not,
  /** Complement */
  ptn_comp,
};

typedef enum ParseTreeNodeKind ParseTreeNodeKind;

/** @brief The core of a parse tree node. A node can be an operator, a variable or an integer constant. */
union ParseTreeNodeCore
{
  /** Chilren of the node */
  struct ParseTreeNode *children[3];
  /** Represents a string. Only used if node is an identifier or representing the function next. */
  char *str;
  /** Represents an integer. Only used if node is an integer. */
  long long int val;
};

typedef union ParseTreeNodeCore ParseTreeNodeCore;

/**
 * @brief Represents a node of a parse tree.
 */
struct ParseTreeNode
{
  /** The kind of node */
  ParseTreeNodeKind kind;
  /** The core of the node */
  ParseTreeNodeCore core;
};

typedef struct ParseTreeNode ParseTreeNode;

/** Returns the first child von a parse tree node */
#define parse_tree_node_first_child(node) ((node)->core.children[0])
/** Returns the second child von a parse tree node */
#define parse_tree_node_second_child(node) ((node)->core.children[1])
/** Returns the third child von a parse tree node */
#define parse_tree_node_third_child(node) ((node)->core.children[2])

/** 
 * @brief Represents a parse tree. */
struct ParseTree
{
  /** The root node of the parse tree */
  ParseTreeNode *root;
};

typedef struct ParseTree ParseTree;

/** Creates a parse tree node and returns it.
 * @param kind The kind of parse tree node
 * @return The node
 */
ParseTreeNode *create_parse_tree_node (ParseTreeNodeKind kind);

/** Creates an identifier parse tree leaf and returns it.
 * @param str The string of the identifier
 * @return The node
 */
ParseTreeNode *create_parse_tree_ident_leaf (const char *str);

/** Creates an integer parse tree leaf and returns it.
 * @param val The value of the integer
 * @return The node
 */
ParseTreeNode *create_parse_tree_integer_leaf (long long int val);

/** Deletes a parse tree node and all its children from memory.
 * @param node The root node where the deleting has to begin
 */
void delete_parse_tree_node (ParseTreeNode * node);

/** Creates an empty parse tree and returns it.
 * @return An empty parse tree
 */
ParseTree *create_parse_tree ();

/** Deletes a parse tree and all its nodes from memory.
 * @param tree The tree which has to be deleted
 */
void delete_parse_tree (ParseTree * tree);

/** Pretty prints a parse tree.
 * @param tree The parse tree which has to be printed
 * @param output The file which shout be used for output
 */
void pretty_print_parse_tree (const ParseTree * tree, FILE * output);

#endif
