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
#ifndef _LINKED_LIST_H_
#define _LINKED_LIST_H_

#include "bool.h"

/** @brief Represents a linked list node. */
struct LinkedListNode
{
  /** The element of the node */
  void *element;
  /** The next node in the list */
  struct LinkedListNode *next;
};

typedef struct LinkedListNode LinkedListNode;

/** @brief Represents a linked list. */
struct LinkedList
{
  /** The size of the list */
  int size;
  /** The fist element in the list */
  LinkedListNode *head;
  /** The last element in the list */
  LinkedListNode *tail;
};

typedef struct LinkedList LinkedList;

/** Represents an iterator which is used for iterating over
 * a linked list.
 */
struct LinkedListIterator
{
  /** The current node in the iteration */
  LinkedListNode *cur;
};

typedef struct LinkedListIterator LinkedListIterator;

/** Creates an empty linked list and returns it.
 * @return The empty linked list
 */
LinkedList *create_linked_list ();

/** Deletes a whole linked list from memory.
 * @param list The list which has to be deleted
 */
void delete_linked_list (LinkedList * list);

/** Creates an iterator which is used to iterate over the 
 * corresponding linked list.
 * @param list The corresponding list
 * @return The resulting iterator
 */
LinkedListIterator *create_linked_list_iterator (LinkedList * list);

/** Deletes a linked list iterator from memory.
 * @param iterator The linked list iterator which has to
 * be deleted.
 */
void delete_linked_list_iterator (LinkedListIterator * iterator);

/** Adds an element at the beginning of the linked list.
 * @param list The corresponding list
 * @param element The element which has to be added do the list
 */
void add_element_first_linked_list (LinkedList * list, void *element);

/** Appends an element to the linked list.
 * @param list The corresponding list
 * @param element The element which has to be added do the list
 */
void add_element_last_linked_list (LinkedList * list, void *element);

/** Removes an element from the linked list.
 * @param list The corresponding list
 * @param element The element which has to be deleted from the list
 * @return @ref b_true if the list contained the element
 * and @ref b_false if not
 */
Bool remove_element_linked_list (LinkedList * list, void *element);

/** Returns if there is a next element in the iteration.
 * @param iterator The corresponding iterator
 * @return @ref b_true if there is a next element
 * in the iteration and @ref b_false if not
 */
Bool has_next_linked_list_iterator (LinkedListIterator * iterator);

/** Returns the next element in the iteration.
 * @param iterator The corresponding iterator
 * @return The next element in the iteration
 */
void *next_linked_list_iterator (LinkedListIterator * iterator);

#endif
