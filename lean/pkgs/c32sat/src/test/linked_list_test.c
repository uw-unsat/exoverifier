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
#include <string.h>
#include <stdio.h>
#include <stdlib.h>
#include "linked_list_test.h"
#include "test_logging.h"
#include "../bool.h"
#include "../linked_list.h"
#include "../error_management.h"
#include "../memory_management.h"

void
test_create_delete_linked_list ()
{
  LinkedListNode *node1 = NULL;
  LinkedListNode *node2 = NULL;
  LinkedListNode *node3 = NULL;
  LinkedList *list = NULL;
  int test_int1 = 1;
  int test_int2 = 2;
  int test_int3 = 3;
  init_error_management (stderr);
  init_memory_management ();
  node1 = (LinkedListNode *) malloc_c32sat (sizeof (LinkedListNode));
  node1->element = (void *) &test_int1;
  node2 = (LinkedListNode *) malloc_c32sat (sizeof (LinkedListNode));
  node2->element = (void *) &test_int2;
  node3 = (LinkedListNode *) malloc_c32sat (sizeof (LinkedListNode));
  node3->element = (void *) &test_int3;
  list = create_linked_list ();
  delete_linked_list (list);
  list = create_linked_list ();
  list->head = node1;
  list->tail = node3;
  node1->next = node2;
  node2->next = node3;
  node3->next = NULL;
  delete_linked_list (list);
  finalise_memory_management ();
}

void
test_create_delete_linked_list_iterator ()
{
  LinkedListNode *node = NULL;
  LinkedList *list = NULL;
  LinkedListIterator *iterator = NULL;
  int test_int = 1;
  init_error_management (stderr);
  init_memory_management ();
  node = (LinkedListNode *) malloc_c32sat (sizeof (LinkedListNode));
  node->element = (void *) &test_int;
  node->next = NULL;
  list = create_linked_list ();
  list->head = node;
  list->tail = node;
  iterator = create_linked_list_iterator (list);
  assert (iterator->cur == node);
  delete_linked_list_iterator (iterator);
  delete_linked_list (list);
  finalise_memory_management ();
}

void
test_add_element_first_linked_list ()
{
  LinkedList *list = NULL;
  int test_int1 = 1;
  int test_int2 = 2;
  int test_int3 = 3;
  init_error_management (stderr);
  init_memory_management ();
  list = create_linked_list ();
  add_element_first_linked_list (list, &test_int1);
  assert (list->size == 1);
  assert (list->head == list->tail);
  assert (list->head->element == &test_int1);
  assert (list->tail->element == &test_int1);
  assert (list->head->next == NULL);
  assert (list->tail->next == NULL);
  add_element_first_linked_list (list, &test_int2);
  assert (list->size == 2);
  assert (list->head != list->tail);
  assert (list->head->element == &test_int2);
  assert (list->tail->element == &test_int1);
  assert (list->head->next->element == &test_int1);
  assert (list->tail->next == NULL);
  add_element_first_linked_list (list, &test_int3);
  assert (list->head != list->tail);
  assert (list->size == 3);
  assert (list->head->element == &test_int3);
  assert (list->tail->element == &test_int1);
  assert (list->head->next->element == &test_int2);
  assert (list->head->next->next->element == &test_int1);
  assert (list->tail->next == NULL);
  delete_linked_list (list);
  finalise_memory_management ();
}

void
test_add_element_last_linked_list ()
{
  LinkedList *list = NULL;
  int test_int1 = 1;
  int test_int2 = 2;
  int test_int3 = 3;
  init_error_management (stderr);
  init_memory_management ();
  list = create_linked_list ();
  add_element_last_linked_list (list, &test_int1);
  assert (list->size == 1);
  assert (list->head == list->tail);
  assert (list->head->element == &test_int1);
  assert (list->tail->element == &test_int1);
  assert (list->head->next == NULL);
  assert (list->tail->next == NULL);
  add_element_last_linked_list (list, &test_int2);
  assert (list->size == 2);
  assert (list->head != list->tail);
  assert (list->head->element == &test_int1);
  assert (list->tail->element == &test_int2);
  assert (list->head->next->element == &test_int2);
  assert (list->tail->next == NULL);
  add_element_last_linked_list (list, &test_int3);
  assert (list->size == 3);
  assert (list->head != list->tail);
  assert (list->head->element == &test_int1);
  assert (list->tail->element == &test_int3);
  assert (list->head->next->element == &test_int2);
  assert (list->head->next->next->element == &test_int3);
  assert (list->tail->next == NULL);
  delete_linked_list (list);
  finalise_memory_management ();
}

void
test_remove_element_linked_list ()
{
  LinkedList *list = NULL;
  Bool result = b_false;
  int test_int1 = 1;
  int test_int2 = 2;
  int test_int3 = 3;
  init_error_management (stderr);
  init_memory_management ();
  list = create_linked_list ();
  result = remove_element_linked_list (list, &test_int1);
  assert (!result);
  assert (list->size == 0);
  add_element_last_linked_list (list, &test_int1);
  result = remove_element_linked_list (list, &test_int1);
  assert (result);
  assert (list->size == 0);
  assert (list->head == NULL);
  assert (list->tail == NULL);
  add_element_first_linked_list (list, &test_int1);
  add_element_last_linked_list (list, &test_int2);
  result = remove_element_linked_list (list, &test_int1);
  assert (result);
  assert (list->size == 1);
  assert (list->head == list->tail);
  assert (list->head->element == &test_int2);
  assert (list->tail->element == &test_int2);
  assert (list->head->next == NULL);
  assert (list->tail->next == NULL);
  result = remove_element_linked_list (list, &test_int2);
  assert (result);
  assert (list->size == 0);
  assert (list->head == NULL);
  assert (list->tail == NULL);
  add_element_first_linked_list (list, &test_int1);
  add_element_last_linked_list (list, &test_int2);
  result = remove_element_linked_list (list, &test_int2);
  assert (result);
  assert (list->size == 1);
  assert (list->head == list->tail);
  assert (list->head->element == &test_int1);
  assert (list->tail->element == &test_int1);
  assert (list->head->next == NULL);
  assert (list->tail->next == NULL);
  result = remove_element_linked_list (list, &test_int1);
  assert (result);
  assert (list->size == 0);
  assert (list->head == NULL);
  assert (list->tail == NULL);
  add_element_first_linked_list (list, &test_int1);
  add_element_last_linked_list (list, &test_int2);
  add_element_last_linked_list (list, &test_int3);
  result = remove_element_linked_list (list, &test_int2);
  assert (result);
  assert (list->size == 2);
  assert (list->head != list->tail);
  assert (list->head->element == &test_int1);
  assert (list->tail->element == &test_int3);
  assert (list->head->next == list->tail);
  assert (list->tail->next == NULL);
  result = remove_element_linked_list (list, &test_int1);
  assert (result);
  assert (list->size == 1);
  assert (list->head == list->tail);
  assert (list->head->element == &test_int3);
  assert (list->tail->element == &test_int3);
  assert (list->head->next == NULL);
  assert (list->tail->next == NULL);
  result = remove_element_linked_list (list, &test_int3);
  assert (result);
  assert (list->size == 0);
  assert (list->head == NULL);
  assert (list->tail == NULL);
  delete_linked_list (list);
  finalise_memory_management ();
}

void
test_has_next_linked_list_iterator ()
{
  LinkedList *list = NULL;
  LinkedListIterator *iterator = NULL;
  int test_int = 1;
  init_error_management (stderr);
  init_memory_management ();
  list = create_linked_list ();
  iterator = create_linked_list_iterator (list);
  assert (!has_next_linked_list_iterator (iterator));
  delete_linked_list_iterator (iterator);
  add_element_last_linked_list (list, &test_int);
  iterator = create_linked_list_iterator (list);
  assert (has_next_linked_list_iterator (iterator));
  delete_linked_list_iterator (iterator);
  delete_linked_list (list);
  finalise_memory_management ();
}

void
test_next_linked_list_iterator ()
{
  LinkedList *list = NULL;
  LinkedListIterator *iterator = NULL;
  int test_int1 = 1;
  int test_int2 = 2;
  int test_int3 = 3;
  init_error_management (stderr);
  init_memory_management ();
  list = create_linked_list ();
  add_element_first_linked_list (list, &test_int1);
  add_element_last_linked_list (list, &test_int2);
  add_element_last_linked_list (list, &test_int3);
  iterator = create_linked_list_iterator (list);
  assert (has_next_linked_list_iterator (iterator));
  assert (next_linked_list_iterator (iterator) == &test_int1);
  assert (has_next_linked_list_iterator (iterator));
  assert (next_linked_list_iterator (iterator) == &test_int2);
  assert (has_next_linked_list_iterator (iterator));
  assert (next_linked_list_iterator (iterator) == &test_int3);
  assert (!has_next_linked_list_iterator (iterator));
  delete_linked_list_iterator (iterator);
  delete_linked_list (list);
  finalise_memory_management ();
}

void
run_linked_list_tests ()
{
  run_test (test_create_delete_linked_list);
  run_test (test_create_delete_linked_list_iterator);
  run_test (test_add_element_first_linked_list);
  run_test (test_add_element_last_linked_list);
  run_test (test_remove_element_linked_list);
  run_test (test_has_next_linked_list_iterator);
  run_test (test_next_linked_list_iterator);
}
