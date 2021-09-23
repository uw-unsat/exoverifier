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
#include "stack_test.h"
#include "test_logging.h"
#include "../memory_management.h"
#include "../error_management.h"
#include "../stack.h"

void
test_create_delete_stack ()
{
  Stack *stack = NULL;
  StackEntry *entry1 = NULL;
  StackEntry *entry2 = NULL;
  StackEntry *entry3 = NULL;
  int element1 = 1;
  int element2 = 2;
  int element3 = 3;
  init_error_management (stderr);
  init_memory_management ();
  stack = create_stack ();
  assert (stack != NULL);
  assert (stack->top == NULL);
  delete_stack (stack);
  stack = create_stack ();
  assert (stack != NULL);
  assert (stack->top == NULL);
  entry1 = (StackEntry *) malloc_c32sat (sizeof (StackEntry));
  entry1->element = (void *) &element1;
  entry2 = (StackEntry *) malloc_c32sat (sizeof (StackEntry));
  entry2->element = (void *) &element2;
  entry3 = (StackEntry *) malloc_c32sat (sizeof (StackEntry));
  entry3->element = (void *) &element3;
  stack->top = entry1;
  entry1->next = entry2;
  entry2->next = entry3;
  entry3->next = NULL;
  delete_stack (stack);
  finalise_memory_management ();
}

void
test_push_stack ()
{
  Stack *stack = NULL;
  init_error_management (stderr);
  init_memory_management ();
  stack = create_stack ();
  assert (stack->top == NULL);
  push_stack (stack, (void *) 1);
  assert (stack->top != NULL);
  assert (stack->top->element == (void *) 1);
  assert (stack->top->next == NULL);
  push_stack (stack, (void *) 2);
  assert (stack->top != NULL);
  assert (stack->top->element == (void *) 2);
  assert (stack->top->next->element == (void *) 1);
  assert (stack->top->next->next == NULL);
  push_stack (stack, (void *) 3);
  assert (stack->top != NULL);
  assert (stack->top->element == (void *) 3);
  assert (stack->top->next->element == (void *) 2);
  assert (stack->top->next->next->element == (void *) 1);
  assert (stack->top->next->next->next == NULL);
  delete_stack (stack);
  finalise_memory_management ();
}

void
test_pop_stack ()
{
  Stack *stack = NULL;
  init_error_management (stderr);
  init_memory_management ();
  stack = create_stack ();
  assert (pop_stack (stack) == NULL);
  push_stack (stack, (void *) 1);
  push_stack (stack, (void *) 2);
  push_stack (stack, (void *) 3);
  push_stack (stack, (void *) 4);
  push_stack (stack, (void *) 5);
  assert (pop_stack (stack) == (void *) 5);
  assert (pop_stack (stack) == (void *) 4);
  assert (pop_stack (stack) == (void *) 3);
  assert (pop_stack (stack) == (void *) 2);
  assert (pop_stack (stack) == (void *) 1);
  assert (pop_stack (stack) == NULL);
  delete_stack (stack);
  finalise_memory_management ();
}

void
test_is_empty_stack ()
{
  Stack *stack = NULL;
  init_error_management (stderr);
  init_memory_management ();
  stack = create_stack ();
  assert (is_empty_stack (stack));
  push_stack (stack, (void *) 1);
  assert (!is_empty_stack (stack));
  push_stack (stack, (void *) 2);
  assert (!is_empty_stack (stack));
  pop_stack (stack);
  assert (!is_empty_stack (stack));
  pop_stack (stack);
  assert (is_empty_stack (stack));
  delete_stack (stack);
  finalise_memory_management ();
}

void
run_stack_tests ()
{
  run_test (test_create_delete_stack);
  run_test (test_push_stack);
  run_test (test_pop_stack);
  run_test (test_is_empty_stack);
}
