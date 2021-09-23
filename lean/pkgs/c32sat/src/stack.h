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
#ifndef _STACK_H_
#define _STACK_H_

/** Represents a stack entry. */
struct StackEntry
{
  /** The element of the entry */
  void *element;
  /** The next stack entry */
  struct StackEntry *next;
};

typedef struct StackEntry StackEntry;

/** Represents a stack. */
struct Stack
{
  /** The top element of the stack */
  StackEntry *top;
};

typedef struct Stack Stack;

/** Creates an empty stack and returns it
 * @return The resulting empty stack
 */
Stack *create_stack ();

/** Deletes a whole stack from memory.
 * @param stack The stack which has to be deleted
 */
void delete_stack (Stack * stack);

/** Pushes an element on top of the stack.
 * @param stack The corresponding stack
 * @param element The element which has to be pushed
 */
void push_stack (Stack * stack, void *element);

/** Pops the element on top of the stack and returns it.
 * @param stack The corresponding stack
 * @return The element on top of the stack or NULL if the
 * stack is empty
 */
void *pop_stack (Stack * stack);

/** Returns if the stack is empty */
#define is_empty_stack(stack) ((stack)->top == NULL)

#endif
