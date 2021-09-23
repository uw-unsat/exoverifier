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
#ifndef _PARSE_TREE_ANALYSIS_H_
#define _PARSE_TREE_ANALYSIS_H_

#include "parse_tree.h"
#include "hash_table.h"
#include "bool.h"
#include "linked_list.h"

/** @brief Represents the context of an input variable */
struct VariableContext
{
  /** Determines if the corresponding variable is used 
   * only in boolean context */
  Bool bool;
  /** Start id for the binary encoding */
  int start_id;
};

typedef struct VariableContext VariableContext;

/** Analyses the parse tree, stores the strings of all input
 * variables of the parse tree into the list variables and
 * builds a symbol table containing for every input variable
 * its context and returns it. The context of every variable
 * will be automatically deleted from memory if you call
 * @ref delete_hash_table with delete_data = @ref b_true.
 * @param tree The parse tree which has to be analysed
 * @param variables The list in which the strings of all
 * input variables of the parse tree are stored
 * @param first_free_id The first free id which can be used
 * for encoding later.
 * @return Returns a hash table which acts as a symbol table. 
 * In the hash table for every variable its context is stored. 
 * Use the string of the variable as a key to lookup its context.
 */
HashTable *analyse_parse_tree (ParseTree * tree, LinkedList ** variables,
                               int *first_free_id);

#endif
