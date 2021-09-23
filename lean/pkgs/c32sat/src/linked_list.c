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
#include "linked_list.h"
#include "bool.h"
#include "memory_management.h"

static LinkedListNode *
create_linked_list_node (void *element)
{
  LinkedListNode *node =
    (LinkedListNode *) malloc_c32sat (sizeof (LinkedListNode));
  node->element = element;
  node->next = NULL;
  return node;
}

static void
delete_linked_list_node (LinkedListNode * node)
{
  assert (node != NULL);
  free_c32sat (node, sizeof (LinkedListNode));
}

LinkedList *
create_linked_list ()
{
  LinkedList *list = (LinkedList *) malloc_c32sat (sizeof (LinkedList));
  list->size = 0;
  list->head = NULL;
  list->tail = NULL;
  return list;
}

void
delete_linked_list (LinkedList * list)
{
  LinkedListNode *cur = NULL;
  LinkedListNode *temp = NULL;
  assert (list != NULL);
  cur = list->head;
  while (cur != NULL)
    {
      temp = cur->next;
      delete_linked_list_node (cur);
      cur = temp;
    }
  free_c32sat (list, sizeof (LinkedList));
}

LinkedListIterator *
create_linked_list_iterator (LinkedList * list)
{
  LinkedListIterator *iterator = NULL;
  assert (list != NULL);
  iterator =
    (LinkedListIterator *) malloc_c32sat (sizeof (LinkedListIterator));
  iterator->cur = list->head;
  return iterator;
}

void
delete_linked_list_iterator (LinkedListIterator * iterator)
{
  assert (iterator != NULL);
  free_c32sat (iterator, sizeof (LinkedListIterator));
}

void
add_element_first_linked_list (LinkedList * list, void *element)
{
  LinkedListNode *node = NULL;
  assert (list != NULL);
  node = create_linked_list_node (element);
  if (list->size == 0)
    {
      assert (list->head == NULL && list->tail == NULL);
      list->head = node;
      list->tail = node;
    }
  else
    {
      assert (list->head != NULL && list->tail != NULL);
      node->next = list->head;
      list->head = node;
    }
  list->size++;
}

void
add_element_last_linked_list (LinkedList * list, void *element)
{
  LinkedListNode *node = NULL;
  assert (list != NULL);
  node = create_linked_list_node (element);
  if (list->size == 0)
    {
      assert (list->head == NULL && list->tail == NULL);
      list->head = node;
      list->tail = node;
    }
  else
    {
      assert (list->head != NULL && list->tail != NULL);
      list->tail->next = node;
      list->tail = node;
    }
  list->size++;
}

Bool
remove_element_linked_list (LinkedList * list, void *element)
{
  Bool found = b_false;
  LinkedListNode *cur = NULL;
  LinkedListNode *prev = NULL;
  assert (list != NULL);
  cur = list->head;
  while (cur != NULL && !found)
    {
      if (cur->element == element)
        {
          found = b_true;
        }
      else
        {
          prev = cur;
          cur = cur->next;
        }
    }
  if (found)
    {
      assert (cur != NULL);
      if (list->size == 1)
        {
          list->head = NULL;
          list->tail = NULL;
        }
      else
        {
          assert (list->size > 1 && list->head != list->tail);
          if (prev != NULL)
            {
              prev->next = cur->next;
            }
          if (list->head == cur)
            {
              list->head = list->head->next;
            }
          if (list->tail == cur)
            {
              assert (prev != NULL);
              list->tail = prev;
            }
        }
      delete_linked_list_node (cur);
      list->size--;
    }
  return found;
}

Bool
has_next_linked_list_iterator (LinkedListIterator * iterator)
{
  assert (iterator != NULL);
  if (iterator->cur == NULL)
    {
      return b_false;
    }
  return b_true;
}

void *
next_linked_list_iterator (LinkedListIterator * iterator)
{
  void *result = NULL;
  assert (iterator != NULL && iterator->cur != NULL);
  result = iterator->cur->element;
  iterator->cur = iterator->cur->next;
  return result;
}
