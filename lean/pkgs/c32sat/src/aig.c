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
#include <limits.h>
#include <stdlib.h>
#include <stdarg.h>
#include <stdio.h>
#include "aig.h"
#include "aig_id_generation.h"
#include "bool.h"
#include "memory_management.h"
#include "error_management.h"
#include "c32sat_math.h"
#include "config.h"
#include "stack.h"
#include "hash_table.h"

#define AIG_PRIME 4093u
#define TWO_LEVEL_MINIMISATION_AIG

static AIG *
create_var_aig (int id, unsigned int hash)
{
  AIG *aig = NULL;
  assert (id > 0);
  aig = (AIG *) malloc_c32sat (sizeof (AIG));
  aig->id = id;
  aig_left_child (aig) = NULL;
  aig_right_child (aig) = NULL;
  aig->hash = hash;
  aig->refs = 1;
  aig->next = NULL;
  return aig;
}

static AIG *
create_and_aig (AIG * left, AIG * right, unsigned int hash)
{
  AIG *aig = NULL;
  assert (left != AIG_FALSE && left != AIG_TRUE
          && right != AIG_FALSE && right != AIG_TRUE);
  aig = (AIG *) malloc_c32sat (sizeof (AIG));
  assert (!is_inverted_aig (aig));
  aig->id = 0;
  aig_left_child (aig) = left;
  aig_right_child (aig) = right;
  aig->hash = hash;
  aig->refs = 1;
  aig->next = NULL;
  return aig;
}

static void
delete_aig (AIG * aig)
{
  if (aig != AIG_FALSE && aig != AIG_TRUE)
    {
      free_c32sat (aig, sizeof (AIG));
    }
}

static void
delete_aig_unique_table_chain (AIG * node)
{
  AIG *temp = node;
  while (node != NULL)
    {
      temp = node->next;
      delete_aig (node);
      node = temp;
    }
}

void
delete_aig_unique_table (AIGUniqueTable * table, Bool delete_entries)
{
  int i = 0;
  assert (table != NULL && table->chains != NULL);
  if ((delete_entries && (table->num_vars + table->num_ands) > 0)
      || (table->ref_overflow_occured))
    {
      for (i = 0; i < table->size; i++)
        {
          delete_aig_unique_table_chain (table->chains[i]);
        }
    }
  free_c32sat (table->chains, sizeof (AIG *) * table->size);
  free_c32sat (table, sizeof (AIGUniqueTable));
}

AIGUniqueTable *
create_aig_unique_table (int power)
{
  AIGUniqueTable *table = NULL;
  int i = 0;
  int size = 0;
  assert (power >= 0);
  size = 1 << min_c32sat_math (power, AIG_UNIQUE_TABLE_MAX_POWER);
  table = (AIGUniqueTable *) malloc_c32sat (sizeof (AIGUniqueTable));
  table->size = size;
  table->num_vars = 0;
  table->num_ands = 0;
  table->ref_overflow_occured = b_false;
  table->chains = (AIG **) malloc_c32sat (sizeof (AIG *) * size);
  for (i = 0; i < size; i++)
    {
      table->chains[i] = NULL;
    }
  return table;
}

static void
delete_aig_unique_table_entry (AIGUniqueTable * table, AIG * aig)
{
  AIG *cur = table->chains[aig->hash & (table->size - 1)];
  AIG *prev = NULL;
  while (cur != aig && cur != NULL)
    {
      prev = cur;
      cur = cur->next;
    }
  assert (cur != NULL);
  if (prev == NULL)
    {
      table->chains[aig->hash & (table->size - 1)] = cur->next;
    }
  else
    {
      prev->next = cur->next;
    }
  if (is_aig_var (cur))
    {
      table->num_vars--;
    }
  else
    {
      assert (is_aig_and (cur));
      table->num_ands--;
    }
  delete_aig (cur);
}

static void
inc_ref_counter (AIGUniqueTable * table, AIG * aig)
{
  AIG *temp = aig_real_address (aig);
  if (aig != AIG_FALSE && aig != AIG_TRUE)
    {
      if (temp->refs < UINT_MAX)
        {
          temp->refs++;
        }
      else
        {
          table->ref_overflow_occured = b_true;
        }
    }
}

static AIG *
inc_ref_counter_and_return (AIGUniqueTable * table, AIG * aig)
{
  inc_ref_counter (table, aig);
  return aig;
}

struct AIGDecRefCounterState
{
  Bool beginning;
  AIG *aig;
};

typedef struct AIGDecRefCounterState AIGDecRefCounterState;

static AIGDecRefCounterState *
create_aig_dec_ref_counter_state (Bool beginning, AIG * aig)
{
  AIGDecRefCounterState *state = NULL;
  assert (aig != NULL);
  state =
    (AIGDecRefCounterState *) malloc_c32sat (sizeof (AIGDecRefCounterState));
  state->beginning = beginning;
  state->aig = aig;
  return state;
}

static void
delete_aig_dec_ref_counter_state (AIGDecRefCounterState * state)
{
  assert (state != NULL);
  free_c32sat (state, sizeof (AIGDecRefCounterState));
}

static void
dec_ref_counter (AIGUniqueTable * table, AIG * aig)
{
  AIG *real_aig = NULL;
  Stack *stack = NULL;
  AIGDecRefCounterState *state = NULL;
  assert (table != NULL);
  if (aig != AIG_FALSE && aig != AIG_TRUE)
    {
      real_aig = aig_real_address (aig);
      if (real_aig->refs > 1)
        {
          real_aig->refs--;
        }
      else
        {
          assert (real_aig->refs == 1);
          if (is_aig_var (real_aig))
            {
              delete_aig_unique_table_entry (table, real_aig);
            }
          else
            {
              stack = create_stack ();
              push_stack (stack,
                          (void *) create_aig_dec_ref_counter_state (b_true,
                                                                     aig));
              while ((state =
                      (AIGDecRefCounterState *) pop_stack (stack)) != NULL)
                {
                  real_aig = aig_real_address (state->aig);
                  if (state->beginning)
                    {
                      if (real_aig->refs > 1)
                        {
                          real_aig->refs--;
                        }
                      else
                        {
                          assert (real_aig->refs == 1);
                          if (is_aig_and (real_aig))
                            {
                              push_stack (stack,
                                          (void *)
                                          create_aig_dec_ref_counter_state
                                          (b_false, state->aig));
                              push_stack (stack,
                                          (void *)
                                          create_aig_dec_ref_counter_state
                                          (b_true,
                                           aig_right_child (real_aig)));
                              push_stack (stack,
                                          (void *)
                                          create_aig_dec_ref_counter_state
                                          (b_true,
                                           aig_left_child (real_aig)));
                            }
                          else
                            {
                              assert (is_aig_var (real_aig));
                              delete_aig_unique_table_entry (table, real_aig);
                            }
                        }
                    }
                  else
                    {
                      delete_aig_unique_table_entry (table, real_aig);
                    }
                  delete_aig_dec_ref_counter_state (state);
                }
              delete_stack (stack);
            }
        }
    }
}

static AIG **
find_var (AIGUniqueTable * table, int id, unsigned int hash)
{
  AIG **result = table->chains + (hash & (table->size - 1));
  AIG *cur = *result;
  Bool found = b_false;
  while (cur != NULL && !found)
    {
      if (is_aig_var (cur) && cur->id == id)
        {
          found = b_true;
        }
      else
        {
          result = &(cur->next);
          cur = *result;
        }
    }
  return result;
}

static AIG **
find_and (AIGUniqueTable * table, AIG * left, AIG * right, unsigned int hash)
{
  AIG **result = table->chains + (hash & (table->size - 1));
  AIG *cur = *result;
  Bool found = b_false;
  AIG *temp1 = NULL;
  AIG *temp2 = NULL;
  if (aig_real_address (left)->hash > aig_real_address (right)->hash)
    {
      temp1 = right;
      temp2 = left;
    }
  else
    {
      temp1 = left;
      temp2 = right;
    }
  while (cur != NULL && !found)
    {
      if (is_aig_and (cur) && (aig_left_child (cur) == temp1)
          && (aig_right_child (cur) == temp2))
        {
          found = b_true;
        }
      else
        {
          result = &(cur->next);
          cur = *result;
        }
    }
  return result;
}

static void
enlarge_aig_unique_table (AIGUniqueTable ** table)
{
  int i = 0;
  unsigned int hash = 0;
  AIGUniqueTable *new_table =
    create_aig_unique_table (log2_c32sat_math ((*table)->size) + 1);
  AIG *temp = NULL;
  AIG *cur = NULL;
  for (i = 0; i < (*table)->size; i++)
    {
      cur = (*table)->chains[i];
      while (cur != NULL)
        {
          temp = cur->next;
          hash = cur->hash & (new_table->size - 1);
          cur->next = new_table->chains[hash];
          new_table->chains[hash] = cur;
          cur = temp;
        }
    }
  new_table->num_vars = (*table)->num_vars;
  new_table->num_ands = (*table)->num_ands;
  delete_aig_unique_table (*table, b_false);
  *table = new_table;
}

AIG *
var_aig (AIGUniqueTable ** table, int id)
{
  AIG **lookup = NULL;
  assert (table != NULL && *table != NULL && id > 0);
  lookup = find_var (*table, id, (unsigned int)id);
  if (*lookup == NULL)
    {
      if ((*table)->num_vars + (*table)->num_ands ==
          ext_number_of_supported_aigs)
        {
          if (!ext_too_many_aigs_error_occured)
            {
              error (e_aig_too_many_aigs, 0, 0,
                     ext_number_of_supported_aigs, NULL);
            }
          return AIG_FALSE;
        }
      if (((*table)->size < AIG_UNIQUE_TABLE_MAX_SIZE)
          && (((*table)->num_vars + (*table)->num_ands) == (*table)->size))
        {
          enlarge_aig_unique_table (table);
          lookup = find_var (*table, id, (unsigned int)id);
        }
      *lookup = create_var_aig (id, (unsigned int)id);
      (*table)->num_vars++;
    }
  else
    {
      inc_ref_counter (*table, *lookup);
    }
  return *lookup;
}

AIG *
and_aig (AIGUniqueTable ** table, AIG * left, AIG * right)
{
  unsigned int hash = 0;
  AIG **lookup = NULL;
  AIG *real_left = NULL;
  AIG *real_right = NULL;
  assert (table != NULL && *table != NULL);
  if (left == AIG_FALSE || right == AIG_FALSE)
    {
      return AIG_FALSE;
    }
  if (left == AIG_TRUE)
    {
      return inc_ref_counter_and_return (*table, right);
    }
TRY_AGAIN:
  if (right == AIG_TRUE || (left == right))
    {
      return inc_ref_counter_and_return (*table, left);
    }
  if (left == invert_aig (right))
    {
      return AIG_FALSE;
    }
  real_left = aig_real_address (left);
  real_right = aig_real_address (right);
  if (ext_two_level_opt)
    {
      /* 2 level minimization rules for AIGs */
      /* first rule of contradiction */
      if (is_aig_and (real_left) && !is_inverted_aig (left))
        {
          if (aig_left_child (real_left) == invert_aig (right)
              || aig_right_child (real_left) == invert_aig (right))
            {
              return AIG_FALSE;
            }
        }
      /* use commutativity */
      if (is_aig_and (real_right) && !is_inverted_aig (right))
        {
          if (aig_left_child (real_right) == invert_aig (left)
              || aig_right_child (real_right) == invert_aig (left))
            {
              return AIG_FALSE;
            }
        }
      /* second rule of contradiction */
      if (is_aig_and (real_right) && is_aig_and (real_left)
          && !is_inverted_aig (left) && !is_inverted_aig (right))
        {
          if (aig_left_child (real_left) ==
              invert_aig (aig_left_child (real_right))
              || aig_left_child (real_left) ==
              invert_aig (aig_right_child (real_right))
              || aig_right_child (real_left) ==
              invert_aig (aig_left_child (real_right))
              || aig_right_child (real_left) ==
              invert_aig (aig_right_child (real_right)))
            {
              return AIG_FALSE;
            }
        }
      /* first rule of subsumption */
      if (is_aig_and (real_left) && is_inverted_aig (left))
        {
          if (aig_left_child (real_left) == invert_aig (right)
              || aig_right_child (real_left) == invert_aig (right))
            {
              return inc_ref_counter_and_return (*table, right);
            }
        }
      /* use commutativity */
      if (is_aig_and (real_right) && is_inverted_aig (right))
        {
          if (aig_left_child (real_right) == invert_aig (left)
              || aig_right_child (real_right) == invert_aig (left))
            {
              return inc_ref_counter_and_return (*table, left);
            }
        }
      /* second rule of subsumption */
      if (is_aig_and (real_right) && is_aig_and (real_left)
          && is_inverted_aig (left) && !is_inverted_aig (right))
        {
          if (aig_left_child (real_left) ==
              invert_aig (aig_left_child (real_right))
              || aig_left_child (real_left) ==
              invert_aig (aig_right_child (real_right))
              || aig_right_child (real_left) ==
              invert_aig (aig_left_child (real_right))
              || aig_right_child (real_left) ==
              invert_aig (aig_right_child (real_right)))
            {
              return inc_ref_counter_and_return (*table, right);
            }
        }
      /* use commutativity */
      if (is_aig_and (real_right) && is_aig_and (real_left)
          && !is_inverted_aig (left) && is_inverted_aig (right))
        {
          if (aig_left_child (real_left) ==
              invert_aig (aig_left_child (real_right))
              || aig_left_child (real_left) ==
              invert_aig (aig_right_child (real_right))
              || aig_right_child (real_left) ==
              invert_aig (aig_left_child (real_right))
              || aig_right_child (real_left) ==
              invert_aig (aig_right_child (real_right)))
            {
              return inc_ref_counter_and_return (*table, left);
            }
        }
      /* rule of resolution */
      if (is_aig_and (real_right) && is_aig_and (real_left)
          && is_inverted_aig (left) && is_inverted_aig (right))
        {
          if ((aig_left_child (real_left) == aig_left_child (real_right)
               && aig_right_child (real_left) ==
               invert_aig (aig_right_child (real_right)))
              || (aig_left_child (real_left) == aig_right_child (real_right)
                  && aig_right_child (real_left) ==
                  invert_aig (aig_left_child (real_right))))
            {
              return inc_ref_counter_and_return (*table,
                                      invert_aig (aig_left_child
                                                  (real_left)));
            }
        }
      /* use commutativity */
      if (is_aig_and (real_right) && is_aig_and (real_left)
          && is_inverted_aig (left) && is_inverted_aig (right))
        {
          if ((aig_right_child (real_right) == aig_right_child (real_left)
               && aig_left_child (real_right) ==
               invert_aig (aig_left_child (real_left)))
              || (aig_right_child (real_right) == aig_left_child (real_left)
                  && aig_left_child (real_right) ==
                  invert_aig (aig_right_child (real_left))))
            {
              return inc_ref_counter_and_return (*table,
                                      invert_aig (aig_right_child
                                                  (real_right)));
            }
        }
      /* asymmetric rule of idempotency */
      if (is_aig_and (real_left) && !is_inverted_aig (left))
        {
          if (aig_left_child (real_left) == right
              || aig_right_child (real_left) == right)
            {
              return inc_ref_counter_and_return (*table, left);
            }
        }
      /* use commutativity */
      if (is_aig_and (real_right) && !is_inverted_aig (right))
        {
          if (aig_left_child (real_right) == left
              || aig_right_child (real_right) == left)
            {
              return inc_ref_counter_and_return (*table, right);
            }
        }
      /* symmetric rule of idempotency */
      if (is_aig_and (real_right) && is_aig_and (real_left)
          && !is_inverted_aig (left) && !is_inverted_aig (right))
        {
          if (aig_left_child (real_left) == aig_left_child (real_right)
              || aig_right_child (real_left) == aig_left_child (real_right))
            {
              right = aig_right_child (real_right);
              goto TRY_AGAIN;
            }
        }
      /* use commutativity */
      if (is_aig_and (real_right) && is_aig_and (real_left)
          && !is_inverted_aig (left) && !is_inverted_aig (right))
        {
          if (aig_left_child (real_left) == aig_right_child (real_right)
              || aig_right_child (real_left) == aig_right_child (real_right))
            {
              right = aig_left_child (real_right);
              goto TRY_AGAIN;
            }
        }
      /* asymmetric rule of substitution */
      if (is_aig_and (real_left) && is_inverted_aig (left))
        {
          if (aig_right_child (real_left) == right)
            {
              left = invert_aig (aig_left_child (real_left));
              goto TRY_AGAIN;
            }
          if (aig_left_child (real_left) == right)
            {
              left = invert_aig (aig_right_child (real_left));
              goto TRY_AGAIN;
            }
        }
      /* use commutativity */
      if (is_aig_and (real_right) && is_inverted_aig (right))
        {
          if (aig_left_child (real_right) == left)
            {
              right = invert_aig (aig_right_child (real_right));
              goto TRY_AGAIN;
            }
          if (aig_right_child (real_right) == left)
            {
              right = invert_aig (aig_left_child (real_right));
              goto TRY_AGAIN;
            }
        }
      /* symmetric rule of substitution */
      if (is_aig_and (real_left) && is_inverted_aig (left)
          && is_aig_and (real_right) && !is_inverted_aig (right))
        {
          if ((aig_right_child (real_left) == aig_left_child (real_right))
              || (aig_right_child (real_left) ==
                  aig_right_child (real_right)))
            {
              left = invert_aig (aig_left_child (real_left));
              goto TRY_AGAIN;
            }
          if ((aig_left_child (real_left) == aig_left_child (real_right)) ||
              (aig_left_child (real_left) == aig_right_child (real_right)))
            {
              left = invert_aig (aig_right_child (real_left));
              goto TRY_AGAIN;
            }
        }
      /* use commutativity */
      if (is_aig_and (real_right) && is_inverted_aig (right)
          && is_aig_and (real_left) && !is_inverted_aig (left))
        {
          if ((aig_left_child (real_right) == aig_right_child (real_left))
              || (aig_left_child (real_right) == aig_left_child (real_left)))
            {
              right = invert_aig (aig_right_child (real_right));
              goto TRY_AGAIN;
            }
          if ((aig_right_child (real_right) == aig_right_child (real_left)) ||
              (aig_right_child (real_right) == aig_left_child (real_left)))
            {
              right = invert_aig (aig_left_child (real_right));
              goto TRY_AGAIN;
            }
        }
    }
  hash = AIG_PRIME * (real_left->hash + real_right->hash);
  lookup = find_and (*table, left, right, hash);
  if (*lookup == NULL)
    {
      if ((*table)->num_vars + (*table)->num_ands ==
          ext_number_of_supported_aigs)
        {
          if (!ext_too_many_aigs_error_occured)
            {
              error (e_aig_too_many_aigs, 0, 0,
                     ext_number_of_supported_aigs, NULL);
            }
          return AIG_FALSE;
        }
      if (((*table)->size < AIG_UNIQUE_TABLE_MAX_SIZE)
          && (((*table)->num_vars + (*table)->num_ands) == (*table)->size))
        {
          enlarge_aig_unique_table (table);
          lookup = find_and (*table, left, right, hash);
        }
      if (real_left->hash > real_right->hash)
        {
          *lookup = create_and_aig (right, left, hash);
        }
      else
        {
          *lookup = create_and_aig (left, right, hash);
        }
      inc_ref_counter (*table, left);
      inc_ref_counter (*table, right);
      (*table)->num_ands++;
    }
  else
    {
      inc_ref_counter (*table, *lookup);
    }
  return *lookup;
}

AIG *
or_aig (AIGUniqueTable ** table, AIG * left, AIG * right)
{
  assert (table != NULL && *table != NULL);
  return invert_aig (and_aig (table, invert_aig (left), invert_aig (right)));
}

AIG *
imp_aig (AIGUniqueTable ** table, AIG * left, AIG * right)
{
  assert (table != NULL && *table != NULL);
  return invert_aig (and_aig (table, left, invert_aig (right)));
}

AIG *
dimp_aig (AIGUniqueTable ** table, AIG * left, AIG * right)
{
  AIG *dimp = NULL;
  AIG *dimp_left = NULL;
  AIG *dimp_right = NULL;
  assert (table != NULL && *table != NULL);
  dimp_left = invert_aig (and_aig (table, left, invert_aig (right)));
  dimp_right = invert_aig (and_aig (table, invert_aig (left), right));
  dimp = and_aig (table, dimp_left, dimp_right);
  release_aig (table, dimp_left);
  release_aig (table, dimp_right);
  return dimp;
}

AIG *
xor_aig (AIGUniqueTable ** table, AIG * left, AIG * right)
{
  assert (table != NULL && *table != NULL);
  return invert_aig (dimp_aig (table, left, right));
}

AIG *
copy_aig (AIGUniqueTable ** table, AIG * aig)
{
  assert (table != NULL && *table != NULL);
  if (aig == AIG_FALSE || aig == AIG_TRUE)
    {
      return aig;
    }
  return inc_ref_counter_and_return (*table, aig);
}

void
release_aig (AIGUniqueTable ** table, AIG * aig)
{
  assert (table != NULL && *table != NULL);
  if (aig != AIG_FALSE && aig != AIG_TRUE)
    {
      dec_ref_counter (*table, aig);
    }
}

static AIG *
op_aig_array (AIG
              * (*f_ptr) (AIGUniqueTable **, AIG *,
                          AIG *), AIGUniqueTable ** table,
              AIG ** aigs, int size)
{
  AIG *temp = NULL;
  AIG *result = NULL;
  int i = 0;
  assert (f_ptr != NULL && table != NULL && *table != NULL && aigs != NULL
          && size >= 3);
  result = f_ptr (table, aigs[0], aigs[1]);
  for (i = 2; i < size; i++)
    {
      temp = result;
      result = f_ptr (table, temp, aigs[i]);
      release_aig (table, temp);
    }
  return result;
}

AIG *
and_aig_array (AIGUniqueTable ** table, AIG ** aigs, int size)
{
  assert (table != NULL && *table != NULL && aigs != NULL && size >= 3);
  return op_aig_array (and_aig, table, aigs, size);
}

AIG *
or_aig_array (AIGUniqueTable ** table, AIG ** aigs, int size)
{
  assert (table != NULL && *table != NULL && aigs != NULL && size >= 3);
  return op_aig_array (or_aig, table, aigs, size);
}

AIG *
dimp_aig_array (AIGUniqueTable ** table, AIG ** aigs, int size)
{
  assert (table != NULL && *table != NULL && aigs != NULL && size >= 3);
  return op_aig_array (dimp_aig, table, aigs, size);
}

AIG *
xor_aig_array (AIGUniqueTable ** table, AIG ** aigs, int size)
{
  assert (table != NULL && *table != NULL && aigs != NULL && size >= 3);
  return op_aig_array (xor_aig, table, aigs, size);
}

AIG *
and_aig_va_list (AIGUniqueTable ** table, int num_aigs, ...)
{
  AIG *temp[num_aigs];
  AIG *result = NULL;
  int i = 0;
  va_list ap;
  assert (table != NULL && *table != NULL && num_aigs >= 3);
  va_start (ap, num_aigs);
  for (i = 0; i < num_aigs; i++)
    {
      temp[i] = va_arg (ap, AIG *);
    }
  result = and_aig_array (table, temp, num_aigs);
  va_end (ap);
  return result;
}

AIG *
or_aig_va_list (AIGUniqueTable ** table, int num_aigs, ...)
{
  AIG *temp[num_aigs];
  AIG *result = NULL;
  int i = 0;
  va_list ap;
  assert (table != NULL && *table != NULL && num_aigs >= 3);
  va_start (ap, num_aigs);
  for (i = 0; i < num_aigs; i++)
    {
      temp[i] = va_arg (ap, AIG *);
    }
  result = or_aig_array (table, temp, num_aigs);
  va_end (ap);
  return result;
}

AIG *
dimp_aig_va_list (AIGUniqueTable ** table, int num_aigs, ...)
{
  AIG *temp[num_aigs];
  AIG *result = NULL;
  int i = 0;
  va_list ap;
  assert (table != NULL && *table != NULL && num_aigs >= 3);
  va_start (ap, num_aigs);
  for (i = 0; i < num_aigs; i++)
    {
      temp[i] = va_arg (ap, AIG *);
    }
  result = dimp_aig_array (table, temp, num_aigs);
  va_end (ap);
  return result;
}

AIG *
xor_aig_va_list (AIGUniqueTable ** table, int num_aigs, ...)
{
  AIG *temp[num_aigs];
  AIG *result = NULL;
  int i = 0;
  va_list ap;
  assert (table != NULL && *table != NULL && num_aigs >= 3);
  va_start (ap, num_aigs);
  for (i = 0; i < num_aigs; i++)
    {
      temp[i] = va_arg (ap, AIG *);
    }
  result = xor_aig_array (table, temp, num_aigs);
  va_end (ap);
  return result;
}

AIG *
full_add_aig (AIGUniqueTable ** table, AIG * x, AIG * y,
              AIG * cin, AIG ** cout)
{
  AIG *cout_ands[3];
  assert (table != NULL && *table != NULL && cout != NULL);
  cout_ands[0] = and_aig (table, x, cin);
  cout_ands[1] = and_aig (table, y, cin);
  cout_ands[2] = and_aig (table, x, y);
  *cout = or_aig_array (table, cout_ands, 3);
  release_aig (table, cout_ands[0]);
  release_aig (table, cout_ands[1]);
  release_aig (table, cout_ands[2]);
  return xor_aig_va_list (table, 3, x, y, cin);
}

void
ripple_compare_aig (AIGUniqueTable ** table, AIG * x,
                    AIG * y, AIG * lt_in, AIG * eq_in,
                    AIG * gt_in, AIG ** lt_out, AIG ** eq_out, AIG ** gt_out)
{
  AIG *eq_and_not_x_and_y = NULL;
  AIG *eq_and_x_and_not_y = NULL;
  AIG *x_dimp_y = NULL;
  AIG *lt = NULL;
  AIG *eq = NULL;
  AIG *gt = NULL;
  assert (table != NULL && *table != NULL && lt_out != NULL && eq_out != NULL
          && gt_out != NULL);
  lt =
    and_aig_va_list (table, 3, lt_in, invert_aig (eq_in), invert_aig (gt_in));
  eq =
    and_aig_va_list (table, 3, invert_aig (lt_in), eq_in, invert_aig (gt_in));
  gt =
    and_aig_va_list (table, 3, invert_aig (lt_in), invert_aig (eq_in), gt_in);
  eq_and_not_x_and_y = and_aig_va_list (table, 3, eq, invert_aig (x), y);
  x_dimp_y = dimp_aig (table, x, y);
  eq_and_x_and_not_y = and_aig_va_list (table, 3, eq, x, invert_aig (y));
  *lt_out = or_aig (table, lt, eq_and_not_x_and_y);
  *eq_out = and_aig (table, eq, x_dimp_y);
  *gt_out = or_aig (table, gt, eq_and_x_and_not_y);
  release_aig (table, eq_and_x_and_not_y);
  release_aig (table, x_dimp_y);
  release_aig (table, eq_and_not_x_and_y);
  release_aig (table, lt);
  release_aig (table, eq);
  release_aig (table, gt);
}

#define PRINT_AIG_INITIAL_HASHTABLE_POWER 10

static unsigned int
compute_hash_value_print_aig (void *key)
{
  assert (!is_inverted_aig ((AIG *) key));
  assert (((AIG *) key)->id > 0);
  return (unsigned int) ((AIG *) key)->id;
}

static unsigned int
compute_equals_print_aig (void *key1, void *key2)
{
  return key1 == key2;
}

static int
count_aig_inputs (AIG * aig)
{
  HashTable *table = NULL;
  Stack *stack = NULL;
  AIG *cur = NULL;
  AIG *left = NULL;
  AIG *right = NULL;
  int res = 0;

  cur = aig_real_address (aig);
  table = create_hash_table (PRINT_AIG_INITIAL_HASHTABLE_POWER,
                             compute_hash_value_print_aig,
                             compute_equals_print_aig, NULL);
  stack = create_stack ();
  push_stack (stack, (void *) cur);
  (void) retrieve_aig_id (cur);

  while ((cur = (AIG *) pop_stack (stack)) != NULL)
    {
      assert (!is_inverted_aig (cur));

      if (is_aig_and (cur))
        {
          left = aig_real_address (aig_left_child (cur));
          right = aig_real_address (aig_right_child (cur));

          (void) retrieve_aig_id (left);
          (void) retrieve_aig_id (right);

          if (lookup_hash_table (&table, (void *) right) == NULL)
            {
              insert_data_hash_table (&table, (void *) right, (void *) right);
              push_stack (stack, (void *) right);
            }

          if (lookup_hash_table (&table, (void *) left) == NULL)
            {
              insert_data_hash_table (&table, (void *) left, (void *) left);
              push_stack (stack, (void *) left);
            }
        }
      else
        res++;
    }
  delete_stack (stack);
  delete_hash_table (table, b_false);

  return res;
}

static unsigned int
encode_unsigned_aig_id (int id)
{
  return (unsigned int) ((id < 0) ? 1 - 2 * id : 2 * id);
}

static void
print_aig_inputs (AIG * aig, FILE * file)
{
  HashTable *table = NULL;
  Stack *stack = NULL;
  AIG *cur = NULL;
  AIG *left = NULL;
  AIG *right = NULL;

  cur = aig_real_address (aig);
  table = create_hash_table (PRINT_AIG_INITIAL_HASHTABLE_POWER,
                             compute_hash_value_print_aig,
                             compute_equals_print_aig, NULL);
  stack = create_stack ();
  push_stack (stack, (void *) cur);
  while ((cur = (AIG *) pop_stack (stack)) != NULL)
    {
      assert (!is_inverted_aig (cur));

      if (is_aig_and (cur))
        {
          left = aig_real_address (aig_left_child (cur));
          right = aig_real_address (aig_right_child (cur));

          if (lookup_hash_table (&table, (void *) right) == NULL)
            {
              insert_data_hash_table (&table, (void *) right, (void *) right);
              push_stack (stack, (void *) right);
            }

          if (lookup_hash_table (&table, (void *) left) == NULL)
            {
              insert_data_hash_table (&table, (void *) left, (void *) left);
              push_stack (stack, (void *) left);
            }
        }
      else
        fprintf (file, "%u\n",
                 encode_unsigned_aig_id (retrieve_aig_id (cur)));
    }
  delete_stack (stack);
  delete_hash_table (table, b_false);
}

void
print_aig (AIG * aig, AIGUniqueTable * unique_table, FILE * output)
{
  HashTable *table = NULL;
  Stack *stack = NULL;
  AIG *cur = NULL;
  AIG *left = NULL;
  AIG *right = NULL;
  int cur_id = 0;
  int left_id = 0;
  int right_id = 0;
  int inputs = 0;
  assert (unique_table != NULL && output != NULL);
  if (aig == AIG_TRUE)
    {
      assert ((unique_table->num_ands) == 0 && (unique_table->num_vars == 0));
      fprintf (output, "aag 0 0 0 1 0\n1\n");
    }
  else if (aig == AIG_FALSE)
    {
      assert ((unique_table->num_ands) == 0 && (unique_table->num_vars == 0));
      fprintf (output, "aag 0 0 0 1 0\n0\n");
    }
  else if (is_aig_var (aig_real_address (aig)))
    {
      assert ((unique_table->num_ands) == 0 && (unique_table->num_vars == 1));
      cur_id = aig_real_address (aig)->id;
      fprintf (output, "aag %d 1 0 1 0\n", cur_id);
      cur_id <<= 1;
      assert (aig_real_address (aig)->id == cur_id / 2);
      fprintf (output, "%d\n", cur_id);
      if (is_inverted_aig (aig))
        {
          fprintf (output, "%d\n", cur_id + 1);
        }
      else
        {
          fprintf (output, "%d\n", cur_id);
        }
    }
  else
    {
      inputs = count_aig_inputs (aig);
      cur = aig_real_address (aig);
      fprintf (output, "aag %d %d %d 1 %d\n",
               unique_table->num_vars + unique_table->num_ands,
               inputs, 0, unique_table->num_ands);
      print_aig_inputs (aig, output);
      fprintf (output, "%u\n",
               encode_unsigned_aig_id (retrieve_aig_id (aig)));
      table =
        create_hash_table (PRINT_AIG_INITIAL_HASHTABLE_POWER,
                           compute_hash_value_print_aig,
                           compute_equals_print_aig, NULL);
      stack = create_stack ();
      push_stack (stack, (void *) cur);
      while ((cur = (AIG *) pop_stack (stack)) != NULL)
        {
          assert (!is_inverted_aig (cur));
          cur_id = retrieve_aig_id (cur);
          left_id = retrieve_aig_id (aig_left_child (cur));
          right_id = retrieve_aig_id (aig_right_child (cur));
          fprintf (output, "%u %u %u\n",
                   encode_unsigned_aig_id (cur_id),
                   encode_unsigned_aig_id (left_id),
                   encode_unsigned_aig_id (right_id));
          left = aig_real_address (aig_left_child (cur));
          right = aig_real_address (aig_right_child (cur));
          if (is_aig_and (right))
            {
              if (lookup_hash_table (&table, (void *) right) == NULL)
                {
                  insert_data_hash_table (&table, (void *) right,
                                          (void *) right);
                  push_stack (stack, (void *) right);
                }
            }
          if (is_aig_and (left))
            {
              if (lookup_hash_table (&table, (void *) left) == NULL)
                {
                  insert_data_hash_table (&table, (void *) left,
                                          (void *) left);
                  push_stack (stack, (void *) left);
                }
            }
        }
      delete_stack (stack);
      delete_hash_table (table, b_false);
    }
}
