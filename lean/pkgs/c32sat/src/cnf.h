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
#ifndef _CNF_H_
#define _CNF_H_

#include <stdio.h>
#include "linked_list.h"
#include "bool.h"

/** @brief Represents a CNF clause */
struct CNFClause
{
  /** The size of the clause */
  int size;
  /** The elements of the clause */
  int *elements;
};

typedef struct CNFClause CNFClause;

/** @brief Represents a CNF. */
struct CNF
{
  /** The list of clauses */
  LinkedList *clause_list;
  /** The maximum id of all variables in the cnf */
  int max_var;
  /** The elements of the current clause which is
   *  not complete yet */
  int *cur_clause_elements;
  /** The position in the current clause which is
   * not complete yet */
  int cur_clause_pos;
  /** The size of the current clause which is
   * not complete yet */
  int cur_clause_size;
  /** Determines if too many CNF clauses should have
   * been created. See @ref ext_number_of_supported_cnf_clauses.
   */
  Bool too_many_cnf_clauses_error_occured;
};

typedef struct CNF CNF;

/** @brief Represents an iterator which is used to iterate over
 * a CNF.*/
struct CNFIterator
{
  /** The iterator which is used to iteratte over the list
   * of clauses */
  LinkedListIterator *list_iterator;
  /** The current clause in the iteration */
  CNFClause *cur_clause;
  /** The position in the current clause */
  int cur_clause_pos;
};

typedef struct CNFIterator CNFIterator;

/** Creates an empty CNF and returns it.
 * @return The empty CNF
 */
CNF *create_cnf ();

/** Deletes a CNF and all its clauses from memory.
 * @param cnf The CNF which has to be deleted
 * */
void delete_cnf (CNF * cnf);

/** Adds a variable to the current clause in the CNF.
 * @param cnf The corresponding
 * @param x The variable which has to be added. If x
 * is negative then !x is meant. 0 means end of clause.
 */
void add_cnf (CNF * cnf, int x);

/** Creates an iterator for the CNF cnf and returns it.
 * @param cnf The corresponding cnf
 * @return The iterator for cnf
 */
CNFIterator *create_cnf_iterator (CNF * cnf);

/** Deletes an iterator from memory 
 * @param iterator The iterator which has to be deleted.
 */
void delete_cnf_iterator (CNFIterator * iterator);

/** Returns if there is a next element in the iteration.
 * @param iterator The corresponding iterator
 * @return @ref b_true if there is a next element
 * in the iteration and @ref b_false if not
 */
Bool has_next_cnf_iterator (CNFIterator * iterator);

/** Returns the next element in the iteration.
 * @param iterator The corresponding iterator
 * @return The id of the variable in the iteration.
 * If the end of the current clause is reached then
 * 0 is returned.
 */
int next_cnf_iterator (CNFIterator * iterator);

/** Prints a CNF to a file.
 * @param cnf The CNF which has to be printed
 * @param output The file to which the CNF has to be written
 */
void print_cnf (CNF * cnf, FILE * output);

/** Returns the number of variables of a CNF.
 * Variables may be missing in the CNF. A value of 10 can 
 * mean that there are really the variables 1 to 10 in the
 * CNF, but it can also be the case that some variables are
 * missing. If some variables are missing it means that they
 * do not influence the satisfiabilty result of the CNF.
 */
int get_number_of_cnf_variables (CNF * cnf);

/** Returns the number of clauses of a CNF.
 * @param cnf The corresponding CNF
 * @return The number of clauses
 */
int get_number_of_cnf_clauses (CNF * cnf);

#endif
