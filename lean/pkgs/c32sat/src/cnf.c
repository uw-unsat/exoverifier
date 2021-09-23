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
#include "cnf.h"
#include "memory_management.h"
#include "error_management.h"
#include "linked_list.h"
#include "bool.h"
#include "c32sat_math.h"
#include "config.h"

#define CLAUSE_INITIAL_SIZE 8   /* must be > 0 */

static CNFClause *
create_cnf_clause (int size, int *elements)
{
  CNFClause *clause = NULL;
  assert (size > 0 && elements != NULL);
  clause = (CNFClause *) malloc_c32sat (sizeof (CNFClause));
  clause->size = size;
  clause->elements = elements;
  return clause;
}

static void
delete_cnf_clause (CNFClause * clause)
{
  assert (clause != NULL && clause->elements != NULL);
  free_c32sat (clause->elements, sizeof (int) * clause->size);
  free_c32sat (clause, sizeof (CNFClause));
}

CNF *
create_cnf ()
{
  CNF *cnf = (CNF *) malloc_c32sat (sizeof (CNF));
  cnf->clause_list = create_linked_list ();
  cnf->max_var = 0;
  cnf->cur_clause_elements = NULL;
  cnf->cur_clause_pos = 0;
  cnf->cur_clause_size = 0;
  cnf->too_many_cnf_clauses_error_occured = b_false;
  return cnf;
}

void
delete_cnf (CNF * cnf)
{
  LinkedListIterator *iterator = NULL;
  assert (cnf != NULL && cnf->clause_list != NULL
          && cnf->cur_clause_elements == NULL);
  iterator = create_linked_list_iterator (cnf->clause_list);
  while (has_next_linked_list_iterator (iterator))
    {
      delete_cnf_clause ((CNFClause *) next_linked_list_iterator (iterator));
    }
  delete_linked_list_iterator (iterator);
  delete_linked_list (cnf->clause_list);
  free_c32sat (cnf, sizeof (CNF));
}

void
add_cnf (CNF * cnf, int x)
{
  CNFClause *clause = NULL;
  assert (cnf != NULL);
  if (cnf->cur_clause_elements == NULL)
    {
      assert (cnf->cur_clause_pos == 0 && cnf->cur_clause_size == 0);
      if (get_number_of_cnf_clauses (cnf) ==
          ext_number_of_supported_cnf_clauses)
        {
          if (!cnf->too_many_cnf_clauses_error_occured)
            {
              error (e_cnf_too_many_cnf_clauses, 0, 0,
                     ext_number_of_supported_cnf_clauses, NULL);
              cnf->too_many_cnf_clauses_error_occured = b_true;
            }
          return;
        }
      assert (x != 0);
      cnf->cur_clause_elements =
        (int *) malloc_c32sat (sizeof (int) * CLAUSE_INITIAL_SIZE);
      cnf->cur_clause_size = CLAUSE_INITIAL_SIZE;
    }
  else if (cnf->cur_clause_pos == cnf->cur_clause_size)
    {
      cnf->cur_clause_size <<= 1;
      assert (cnf->cur_clause_size > 0);
      cnf->cur_clause_elements =
        (int *) realloc_c32sat (cnf->cur_clause_elements,
                                sizeof (int) * (cnf->cur_clause_size >> 1),
                                sizeof (int) * cnf->cur_clause_size);
    }
  if (x != 0)
    {
      cnf->cur_clause_elements[cnf->cur_clause_pos++] = x;
      cnf->max_var = max_c32sat_math (cnf->max_var, abs (x));
    }
  else
    {
      cnf->cur_clause_elements =
        (int *) realloc_c32sat (cnf->cur_clause_elements,
                                sizeof (int) * cnf->cur_clause_size,
                                sizeof (int) * cnf->cur_clause_pos);
      clause =
        create_cnf_clause (cnf->cur_clause_pos, cnf->cur_clause_elements);
      add_element_last_linked_list (cnf->clause_list, clause);
      cnf->cur_clause_elements = NULL;
      cnf->cur_clause_pos = 0;
      cnf->cur_clause_size = 0;
    }
}

CNFIterator *
create_cnf_iterator (CNF * cnf)
{
  CNFIterator *iterator = NULL;
  assert (cnf != NULL);
  iterator = (CNFIterator *) malloc_c32sat (sizeof (CNFIterator));
  iterator->list_iterator = create_linked_list_iterator (cnf->clause_list);
  iterator->cur_clause = NULL;
  iterator->cur_clause_pos = 0;
  return iterator;
}

void
delete_cnf_iterator (CNFIterator * iterator)
{
  assert (iterator != NULL && iterator->cur_clause == NULL);
  delete_linked_list_iterator (iterator->list_iterator);
  free_c32sat (iterator, sizeof (CNFIterator));
}

Bool
has_next_cnf_iterator (CNFIterator * iterator)
{
  if (iterator->cur_clause == NULL)
    {
      return has_next_linked_list_iterator (iterator->list_iterator);
    }
  else
    {
      assert (iterator->cur_clause_pos <= iterator->cur_clause->size);
      return b_true;
    }
}

int
next_cnf_iterator (CNFIterator * iterator)
{
  int result = 0;
  assert (iterator != NULL);
  if (iterator->cur_clause == NULL)
    {
      assert (has_next_linked_list_iterator (iterator->list_iterator));
      iterator->cur_clause =
        (CNFClause *) next_linked_list_iterator (iterator->list_iterator);
      result = iterator->cur_clause->elements[0];
      iterator->cur_clause_pos = 1;
    }
  else if (iterator->cur_clause_pos < iterator->cur_clause->size)
    {
      result = iterator->cur_clause->elements[iterator->cur_clause_pos++];
    }
  else
    {
      assert (iterator->cur_clause_pos == iterator->cur_clause->size);
      result = 0;
      iterator->cur_clause = NULL;
      iterator->cur_clause_pos = 0;
    }
  return result;
}

void
print_cnf (CNF * cnf, FILE * output)
{
  CNFIterator *iterator = NULL;
  int cur = 0;
  assert (cnf != NULL && cnf->cur_clause_elements == NULL
          && cnf->cur_clause_pos == 0 && cnf->cur_clause_size == 0
          && cnf->max_var > 0 && output != NULL);
  fprintf (output, "p cnf %d %d\n", cnf->max_var, cnf->clause_list->size);
  iterator = create_cnf_iterator (cnf);
  while (has_next_cnf_iterator (iterator))
    {
      cur = next_cnf_iterator (iterator);
      if (cur == 0)
        {
          fprintf (output, "0\n");
        }
      else
        {
          fprintf (output, "%d ", cur);
        }
    }
  delete_cnf_iterator (iterator);
}

int
get_number_of_cnf_variables (CNF * cnf)
{
  assert (cnf != NULL);
  return cnf->max_var;
}

int
get_number_of_cnf_clauses (CNF * cnf)
{
  assert (cnf != NULL);
  return cnf->clause_list->size;
}
