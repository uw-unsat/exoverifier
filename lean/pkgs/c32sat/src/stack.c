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
#include <stdlib.h>
#include <assert.h>
#include "memory_management.h"
#include "stack.h"

static StackEntry *
create_stack_entry (void *element)
{
  StackEntry *entry = (StackEntry *) malloc_c32sat (sizeof (StackEntry));
  entry->element = element;
  entry->next = NULL;
  return entry;
}

static void
delete_stack_entry (StackEntry * entry)
{
  assert (entry != NULL);
  free_c32sat (entry, sizeof (StackEntry));
}

struct Stack *
create_stack ()
{
  Stack *stack = (Stack *) malloc_c32sat (sizeof (Stack));
  stack->top = NULL;
  return stack;
}

void
delete_stack (Stack * stack)
{
  StackEntry *cur = NULL;
  StackEntry *temp = NULL;
  assert (stack != NULL);
  cur = stack->top;
  while (cur != NULL)
    {
      temp = cur->next;
      free_c32sat (cur, sizeof (StackEntry));
      cur = temp;
    }
  free_c32sat (stack, sizeof (Stack));
}

void
push_stack (Stack * stack, void *element)
{
  StackEntry *entry = NULL;
  assert (stack != NULL);
  entry = create_stack_entry (element);
  entry->next = stack->top;
  stack->top = entry;
}

void *
pop_stack (Stack * stack)
{
  StackEntry *temp = NULL;
  void *result = NULL;
  assert (stack != NULL);
  temp = stack->top;
  if (temp != NULL)
    {
      result = temp->element;
      stack->top = temp->next;
      delete_stack_entry (temp);
    }
  return result;
}
