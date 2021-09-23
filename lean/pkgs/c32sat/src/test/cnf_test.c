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
#include <limits.h>
#include "cnf_test.h"
#include "test_logging.h"
#include "../memory_management.h"
#include "../error_management.h"
#include "../cnf.h"
#include "../linked_list.h"
#include "../config.h"

void
test_create_delete_cnf ()
{
  CNF *cnf = NULL;
  CNFClause *clause = NULL;
  int *elements = NULL;
  const int size = 3;
  init_error_management (stderr);
  init_memory_management ();
  elements = (int *) malloc_c32sat (sizeof (int) * size);
  elements[0] = 1;
  elements[1] = 2;
  elements[2] = 3;
  clause = (CNFClause *) malloc_c32sat (sizeof (CNFClause));
  clause->size = size;
  clause->elements = elements;
  cnf = create_cnf ();
  add_element_first_linked_list (cnf->clause_list, clause);
  assert (cnf->clause_list->size == 1);
  assert (cnf->max_var == 0);
  assert (cnf->cur_clause_elements == NULL);
  assert (cnf->cur_clause_pos == 0);
  assert (cnf->cur_clause_size == 0);
  assert (cnf->too_many_cnf_clauses_error_occured == b_false);
  delete_cnf (cnf);
  finalise_memory_management ();
}

void
test_create_delete_cnf_list_iterator ()
{
  CNF *cnf = NULL;
  CNFIterator *iterator = NULL;
  init_error_management (stderr);
  init_memory_management ();
  cnf = create_cnf ();
  iterator = create_cnf_iterator (cnf);
  assert (iterator->list_iterator != NULL);
  assert (iterator->cur_clause == NULL);
  assert (iterator->cur_clause_pos == 0);
  delete_cnf_iterator (iterator);
  delete_cnf (cnf);
  finalise_memory_management ();
}

void
test_add_cnf ()
{
  CNF *cnf = NULL;
  CNFClause *temp;
  const int size = 1025;
  int i = 0;
  init_error_management (stderr);
  init_memory_management ();
  cnf = create_cnf ();
  for (i = 0; i < size; i++)
    {
      add_cnf (cnf, i + 1);
      assert (cnf->max_var == i + 1);
    }
  assert (cnf->max_var == 1025);
  add_cnf (cnf, 0);
  assert (cnf->cur_clause_elements == NULL);
  assert (cnf->cur_clause_size == 0);
  assert (cnf->cur_clause_pos == 0);
  assert (cnf->clause_list->size == 1);
  temp = (CNFClause *) cnf->clause_list->head->element;
  assert (temp->size == 1025);
  for (i = 0; i < size; i++)
    {
      assert (temp->elements[i] == (int) i + 1);
    }
  add_cnf (cnf, 1);
  add_cnf (cnf, 0);
  assert (cnf->cur_clause_elements == NULL);
  assert (cnf->cur_clause_size == 0);
  assert (cnf->cur_clause_pos == 0);
  assert (cnf->clause_list->size == 2);
  temp = (CNFClause *) cnf->clause_list->head->next->element;
  assert (temp->size == 1);
  assert (temp->elements[0] == 1);
  delete_cnf (cnf);
  finalise_memory_management ();
}

void
test_has_next_cnf_iterator ()
{
  CNF *cnf = NULL;
  CNFIterator *iterator = NULL;
  int i = 0;
  const int size = 1025;
  init_error_management (stderr);
  init_memory_management ();
  cnf = create_cnf ();
  for (i = 0; i < size; i++)
    {
      add_cnf (cnf, i + 1);
    }
  add_cnf (cnf, 0);
  add_cnf (cnf, 1);
  add_cnf (cnf, 0);
  add_cnf (cnf, -3);
  add_cnf (cnf, -4);
  add_cnf (cnf, 2);
  add_cnf (cnf, 0);
  iterator = create_cnf_iterator (cnf);
  for (i = 0; i < size + 7; i++)
    {
      assert (has_next_cnf_iterator (iterator));
      next_cnf_iterator (iterator);
    }
  assert (!has_next_cnf_iterator (iterator));
  delete_cnf_iterator (iterator);
  delete_cnf (cnf);
  finalise_memory_management ();
}

void
test_next_cnf_iterator ()
{
  CNF *cnf = NULL;
  CNFIterator *iterator = NULL;
  int i = 0;
  const int size = 1025;
  int expected[size + 7];
  init_error_management (stderr);
  init_memory_management ();
  cnf = create_cnf ();
  for (i = 0; i < size; i++)
    {
      expected[i] = i + 1;
      add_cnf (cnf, i + 1);
    }
  add_cnf (cnf, 0);
  expected[size] = 0;
  add_cnf (cnf, 1);
  expected[size + 1] = 1;
  add_cnf (cnf, 0);
  expected[size + 2] = 0;
  add_cnf (cnf, -3);
  expected[size + 3] = -3;
  add_cnf (cnf, -4);
  expected[size + 4] = -4;
  add_cnf (cnf, 2);
  expected[size + 5] = 2;
  add_cnf (cnf, 0);
  expected[size + 6] = 0;
  iterator = create_cnf_iterator (cnf);
  i = 0;
  while (has_next_cnf_iterator (iterator))
    {
      assert (next_cnf_iterator (iterator) == expected[i]);
      i++;
    }
  assert (!has_next_cnf_iterator (iterator));
  delete_cnf_iterator (iterator);
  delete_cnf (cnf);
  finalise_memory_management ();
}

void
test_print_cnf_1 ()
{
  CNF *cnf = NULL;
  FILE *output = NULL;
  init_error_management (stderr);
  init_memory_management ();
  output = fopen ("output/cnf_1_output.txt", "w");
  cnf = create_cnf ();
  add_cnf (cnf, -17);
  add_cnf (cnf, 2);
  add_cnf (cnf, 1);
  add_cnf (cnf, 0);
  add_cnf (cnf, 4);
  add_cnf (cnf, 0);
  add_cnf (cnf, 6);
  add_cnf (cnf, 16);
  add_cnf (cnf, 0);
  print_cnf (cnf, output);
  delete_cnf (cnf);
  finalise_memory_management ();
  fclose (output);
}

void
test_print_cnf_2 ()
{
  CNF *cnf = NULL;
  FILE *output = NULL;
  init_error_management (stderr);
  init_memory_management ();
  output = fopen ("output/cnf_2_output.txt", "w");
  cnf = create_cnf ();
  add_cnf (cnf, 1);
  add_cnf (cnf, 2);
  add_cnf (cnf, 3);
  add_cnf (cnf, -5);
  add_cnf (cnf, 0);
  add_cnf (cnf, 4);
  add_cnf (cnf, 0);
  add_cnf (cnf, 1);
  add_cnf (cnf, 0);
  add_cnf (cnf, 2);
  add_cnf (cnf, 0);
  add_cnf (cnf, -5);
  add_cnf (cnf, 0);
  add_cnf (cnf, -2);
  add_cnf (cnf, 100);
  add_cnf (cnf, 0);
  print_cnf (cnf, output);
  delete_cnf (cnf);
  finalise_memory_management ();
  fclose (output);
}

void
test_print_cnf_3 ()
{
  CNF *cnf = NULL;
  FILE *output = NULL;
  init_error_management (stderr);
  init_memory_management ();
  output = fopen ("output/cnf_3_output.txt", "w");
  cnf = create_cnf ();
  add_cnf (cnf, 1);
  add_cnf (cnf, 2);
  add_cnf (cnf, -3);
  add_cnf (cnf, 4);
  add_cnf (cnf, -5);
  add_cnf (cnf, 6);
  add_cnf (cnf, 7);
  add_cnf (cnf, 8);
  add_cnf (cnf, 9);
  add_cnf (cnf, -10);
  add_cnf (cnf, 11);
  add_cnf (cnf, 12);
  add_cnf (cnf, 13);
  add_cnf (cnf, -14);
  add_cnf (cnf, 15);
  add_cnf (cnf, 16);
  add_cnf (cnf, -17);
  add_cnf (cnf, -18);
  add_cnf (cnf, 0);
  print_cnf (cnf, output);
  delete_cnf (cnf);
  finalise_memory_management ();
  fclose (output);
}

void
test_get_number_of_cnf_variables ()
{
  CNF *cnf = NULL;
  init_error_management (stderr);
  init_memory_management ();
  cnf = create_cnf ();
  assert (get_number_of_cnf_variables (cnf) == 0);
  add_cnf (cnf, 1);
  add_cnf (cnf, 3);
  add_cnf (cnf, 1);
  add_cnf (cnf, 1);
  add_cnf (cnf, 1);
  add_cnf (cnf, 0);
  assert (get_number_of_cnf_variables (cnf) == 3);
  delete_cnf (cnf);
  finalise_memory_management ();
}

void
test_get_number_of_cnf_clauses ()
{
  CNF *cnf = NULL;
  init_error_management (stderr);
  init_memory_management ();
  cnf = create_cnf ();
  assert (get_number_of_cnf_clauses (cnf) == 0);
  add_cnf (cnf, 1);
  add_cnf (cnf, 3);
  add_cnf (cnf, 0);
  assert (get_number_of_cnf_clauses (cnf) == 1);
  add_cnf (cnf, 2);
  add_cnf (cnf, 0);
  assert (get_number_of_cnf_clauses (cnf) == 2);
  delete_cnf (cnf);
  finalise_memory_management ();
}

void
test_cnf_error_too_many_cnf_clauses ()
{
  FILE *err_output =
    fopen ("output/cnf_error_too_many_cnf_clauses_output.txt", "w");
  CNF *cnf = NULL;
  init_error_management (err_output);
  init_memory_management ();
  cnf = create_cnf ();
  ext_number_of_supported_cnf_clauses = 1;
  assert (!cnf->too_many_cnf_clauses_error_occured);
  add_cnf (cnf, 1);
  assert (!cnf->too_many_cnf_clauses_error_occured);
  add_cnf (cnf, 3);
  assert (!cnf->too_many_cnf_clauses_error_occured);
  add_cnf (cnf, 0);
  assert (get_number_of_cnf_clauses (cnf) == 1);
  assert (!cnf->too_many_cnf_clauses_error_occured);
  add_cnf (cnf, -1);
  assert (cnf->too_many_cnf_clauses_error_occured);
  add_cnf (cnf, 0);
  assert (cnf->too_many_cnf_clauses_error_occured);
  assert (get_number_of_cnf_clauses (cnf) == 1);
  add_cnf (cnf, 10);
  add_cnf (cnf, -3);
  add_cnf (cnf, -4);
  add_cnf (cnf, 5);
  add_cnf (cnf, 11);
  add_cnf (cnf, 19);
  add_cnf (cnf, 28);
  add_cnf (cnf, 39);
  add_cnf (cnf, 40);
  add_cnf (cnf, -55);
  add_cnf (cnf, 0);
  assert (cnf->too_many_cnf_clauses_error_occured);
  assert (get_number_of_cnf_clauses (cnf) == 1);
  delete_cnf (cnf);
  finalise_memory_management ();
  fclose (err_output);
  ext_number_of_supported_cnf_clauses =
    CONFIG_DEFAULT_NUMBER_OF_SUPPORTED_CNF_CLAUSES;
}

void
run_cnf_tests ()
{
  run_test (test_create_delete_cnf);
  run_test (test_create_delete_cnf_list_iterator);
  run_test (test_add_cnf);
  run_test (test_has_next_cnf_iterator);
  run_test (test_next_cnf_iterator);
  run_test (test_print_cnf_1);
  check_output ("output/cnf_1_output.txt", "output/cnf_1_expected.txt");
  run_test (test_print_cnf_2);
  check_output ("output/cnf_2_output.txt", "output/cnf_2_expected.txt");
  run_test (test_print_cnf_3);
  check_output ("output/cnf_3_output.txt", "output/cnf_3_expected.txt");
  run_test (test_get_number_of_cnf_variables);
  run_test (test_get_number_of_cnf_clauses);
  run_test (test_cnf_error_too_many_cnf_clauses);
  check_output ("output/cnf_error_too_many_cnf_clauses_expected.txt",
                "output/cnf_error_too_many_cnf_clauses_output.txt");
}
