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
#include <limits.h>
#include "aig_vector_test.h"
#include "test_logging.h"
#include "random_utilities.h"
#include "special_operator.h"
#include "../aig_vector.h"
#include "../memory_management.h"
#include "../error_management.h"
#include "../bool.h"
#include "../c32sat_math.h"
#include "../config.h"

#define AIG_VECTOR_TEST_NUM_RANDOM_TESTS 500

void
test_create_delete_aig_vector ()
{
  AIGVector *aig_vector = NULL;
  int i = 0;
  init_error_management (stderr);
  init_memory_management ();
  aig_vector = create_aig_vector ();
  for (i = 0; i < 32; i++)
    {
      assert (aig_vector->aig[i] == AIG_FALSE);
    }
  assert (aig_vector->undefined == AIG_FALSE);
  delete_aig_vector (aig_vector);
  finalise_memory_management ();
}

void
test_release_aig_vector ()
{
  AIGVector *aig_vector = NULL;
  AIGUniqueTable *table = NULL;
  int i = 0;
  init_error_management (stderr);
  init_memory_management ();
  table = create_aig_unique_table (8);
  aig_vector = create_aig_vector ();
  for (i = 0; i < 32; i++)
    {
      aig_vector->aig[i] = var_aig (&table, i + 1);
    }
  aig_vector->undefined = var_aig (&table, 33);
  assert (table->num_vars == 33);
  assert (table->num_ands == 0);
  release_aig_vector (&table, aig_vector);
  assert (table->num_vars == 0);
  assert (table->num_ands == 0);
  delete_aig_unique_table (table, b_false);
  delete_aig_vector (aig_vector);
  finalise_memory_management ();
}

void
test_copy_aig_vector ()
{
  AIGVector *aig_vector = NULL;
  AIGVector *result = NULL;
  AIGUniqueTable *table = NULL;
  int i = 0;
  init_error_management (stderr);
  init_memory_management ();
  table = create_aig_unique_table (8);
  aig_vector = create_aig_vector ();
  for (i = 0; i < 32; i++)
    {
      aig_vector->aig[i] = var_aig (&table, i + 1);
    }
  aig_vector->undefined = var_aig (&table, 33);
  result = copy_aig_vector (&table, aig_vector);
  for (i = 0; i < 32; i++)
    {
      assert (result->aig[i] == aig_vector->aig[i]);
      assert (result->aig[i]->refs == 2);
      assert (aig_vector->aig[i]->refs == 2);
    }
  assert (is_aig_var (result->undefined));
  assert (result->undefined->refs == 2);
  release_aig_vector (&table, result);
  release_aig_vector (&table, aig_vector);
  delete_aig_vector (result);
  delete_aig_vector (aig_vector);
  delete_aig_unique_table (table, b_false);
  finalise_memory_management ();
}

void
bin_2_aig_vector (const int *bin, int number_of_bits, AIGVector * aig_vector)
{
  int i = 0;
  assert (number_of_bits > 2);
  for (i = 0; i < number_of_bits; i++)
    {
      aig_vector->aig[i] = bin[i] ? AIG_TRUE : AIG_FALSE;
    }
}

void
test_aig_vector_2_long_long (int x)
{
  AIGVector *aig_vector = NULL;
  const int number_of_bits = 32;
  int bin[number_of_bits];
  init_error_management (stderr);
  init_memory_management ();
  aig_vector = create_aig_vector ();
  long_long_2_bin_c32sat_math (x, bin, number_of_bits);
  bin_2_aig_vector (bin, number_of_bits, aig_vector);
  assert (aig_vector_2_long_long (aig_vector) == x);
  delete_aig_vector (aig_vector);
  finalise_memory_management ();
}

void
test_aig_vector_2_long_long_1 ()
{
  test_aig_vector_2_long_long (INT_MAX);
}

void
test_aig_vector_2_long_long_2 ()
{
  test_aig_vector_2_long_long (INT_MIN);
}

void
test_aig_vector_2_long_long_3 ()
{
  test_aig_vector_2_long_long (0);
}

void
test_aig_vector_2_long_long_4 ()
{
  test_aig_vector_2_long_long (1);
}

void
test_aig_vector_2_long_long_5 ()
{
  test_aig_vector_2_long_long (-1);
}

void
test_aig_vector_2_long_long_random ()
{
  run_void_int_function_random (test_aig_vector_2_long_long,
                                AIG_VECTOR_TEST_NUM_RANDOM_TESTS);
}

void
test_long_long_2_aig_vector (int x)
{
  AIGVector *result = NULL;
  init_error_management (stderr);
  init_memory_management ();
  result = create_aig_vector ();
  long_long_2_aig_vector (x, result);
  assert (aig_vector_2_long_long (result) == x);
  assert (result->undefined == AIG_FALSE);
  delete_aig_vector (result);
  finalise_memory_management ();
}

void
test_long_long_2_aig_vector_1 ()
{
  test_long_long_2_aig_vector (INT_MAX);
}

void
test_long_long_2_aig_vector_2 ()
{
  test_long_long_2_aig_vector (INT_MIN);
}

void
test_long_long_2_aig_vector_3 ()
{
  test_long_long_2_aig_vector (0);
}

void
test_long_long_2_aig_vector_4 ()
{
  test_long_long_2_aig_vector (1);
}

void
test_long_long_2_aig_vector_5 ()
{
  test_long_long_2_aig_vector (-1);
}

void
test_long_long_2_aig_vector_random ()
{
  run_void_int_function_random (test_long_long_2_aig_vector,
                                AIG_VECTOR_TEST_NUM_RANDOM_TESTS);
}

void
test_conjunction_aig_vector (int x)
{
  AIGVector *aig_vector = NULL;
  AIGUniqueTable *table = NULL;
  init_error_management (stderr);
  init_memory_management ();
  aig_vector = create_aig_vector ();
  long_long_2_aig_vector (x, aig_vector);
  table = create_aig_unique_table (8);
  if ((x & -1) == -1)
    {
      assert (conjunction_aig_vector (&table, aig_vector) == AIG_TRUE);
    }
  else
    {
      assert (conjunction_aig_vector (&table, aig_vector) == AIG_FALSE);
    }
  assert (aig_vector->undefined == AIG_FALSE);
  delete_aig_vector (aig_vector);
  delete_aig_unique_table (table, b_false);
  finalise_memory_management ();
}

void
test_conjunction_aig_vector_1 ()
{
  test_conjunction_aig_vector (INT_MAX);
}

void
test_conjunction_aig_vector_2 ()
{
  test_conjunction_aig_vector (INT_MIN);
}

void
test_conjunction_aig_vector_3 ()
{
  test_conjunction_aig_vector (0);
}

void
test_conjunction_aig_vector_4 ()
{
  test_conjunction_aig_vector (1);
}

void
test_conjunction_aig_vector_5 ()
{
  test_conjunction_aig_vector (-1);
}

void
test_conjunction_aig_vector_random ()
{
  run_void_int_function_random (test_conjunction_aig_vector,
                                AIG_VECTOR_TEST_NUM_RANDOM_TESTS);
}

void
test_conjunction_aig_vector_releases ()
{
  AIGVector *aig_vector = NULL;
  AIG *result = NULL;
  AIGUniqueTable *table = NULL;
  int i = 0;
  init_error_management (stderr);
  init_memory_management ();
  aig_vector = create_aig_vector ();
  table = create_aig_unique_table (8);
  for (i = 0; i < 32; i++)
    {
      aig_vector->aig[i] = var_aig (&table, i + 1);
    }
  result = conjunction_aig_vector (&table, aig_vector);
  release_aig (&table, result);
  release_aig_vector (&table, aig_vector);
  delete_aig_vector (aig_vector);
  delete_aig_unique_table (table, b_false);
  finalise_memory_management ();
}

void
test_disjunction_aig_vector (int x)
{
  AIGVector *aig_vector = NULL;
  AIGUniqueTable *table = NULL;
  init_error_management (stderr);
  init_memory_management ();
  aig_vector = create_aig_vector ();
  long_long_2_aig_vector (x, aig_vector);
  table = create_aig_unique_table (8);
  if ((x & -1) == 0)
    {
      assert (disjunction_aig_vector (&table, aig_vector) == AIG_FALSE);
    }
  else
    {
      assert (disjunction_aig_vector (&table, aig_vector) == AIG_TRUE);
    }
  assert (aig_vector->undefined == AIG_FALSE);
  delete_aig_vector (aig_vector);
  delete_aig_unique_table (table, b_false);
  finalise_memory_management ();
}

void
test_disjunction_aig_vector_1 ()
{
  test_disjunction_aig_vector (INT_MAX);
}

void
test_disjunction_aig_vector_2 ()
{
  test_disjunction_aig_vector (INT_MIN);
}

void
test_disjunction_aig_vector_3 ()
{
  test_disjunction_aig_vector (0);
}

void
test_disjunction_aig_vector_4 ()
{
  test_disjunction_aig_vector (1);
}

void
test_disjunction_aig_vector_5 ()
{
  test_disjunction_aig_vector (-1);
}

void
test_disjunction_aig_vector_random ()
{
  run_void_int_function_random (test_disjunction_aig_vector,
                                AIG_VECTOR_TEST_NUM_RANDOM_TESTS);
}

void
test_disjunction_aig_vector_releases ()
{
  AIGVector *aig_vector = NULL;
  AIG *result = NULL;
  AIGUniqueTable *table = NULL;
  int i = 0;
  init_error_management (stderr);
  init_memory_management ();
  aig_vector = create_aig_vector ();
  table = create_aig_unique_table (8);
  for (i = 0; i < 32; i++)
    {
      aig_vector->aig[i] = var_aig (&table, i + 1);
    }
  result = disjunction_aig_vector (&table, aig_vector);
  release_aig (&table, result);
  release_aig_vector (&table, aig_vector);
  delete_aig_vector (aig_vector);
  delete_aig_unique_table (table, b_false);
  finalise_memory_management ();
}

void
test_not_aig_vector (int x)
{
  AIGVector *aig_vector = NULL;
  AIGVector *result = NULL;
  AIGUniqueTable *table = NULL;
  init_error_management (stderr);
  init_memory_management ();
  table = create_aig_unique_table (8);
  aig_vector = create_aig_vector ();
  long_long_2_aig_vector (x, aig_vector);
  result = not_aig_vector (&table, aig_vector);
  if (aig_vector_2_long_long (result))
    {
      assert (!x);
    }
  else
    {
      assert (!!x);
    }
  assert (result->undefined == AIG_FALSE);
  delete_aig_vector (result);
  delete_aig_vector (aig_vector);
  delete_aig_unique_table (table, b_false);
  finalise_memory_management ();
}

void
test_not_aig_vector_1 ()
{
  test_not_aig_vector (INT_MAX);
}

void
test_not_aig_vector_2 ()
{
  test_not_aig_vector (INT_MIN);
}

void
test_not_aig_vector_3 ()
{
  test_not_aig_vector (0);
}

void
test_not_aig_vector_4 ()
{
  test_not_aig_vector (1);
}

void
test_not_aig_vector_5 ()
{
  test_not_aig_vector (-1);
}

void
test_not_aig_vector_undefined ()
{
  AIGVector *aig_vector = NULL;
  AIGVector *result = NULL;
  AIGUniqueTable *table = NULL;
  init_error_management (stderr);
  init_memory_management ();
  table = create_aig_unique_table (8);
  aig_vector = create_aig_vector ();
  long_long_2_aig_vector (0, aig_vector);
  result = not_aig_vector (&table, aig_vector);
  assert (result->undefined == AIG_FALSE);
  delete_aig_vector (result);
  aig_vector->undefined = AIG_TRUE;
  result = not_aig_vector (&table, aig_vector);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  delete_aig_vector (aig_vector);
  delete_aig_unique_table (table, b_false);
  finalise_memory_management ();
}

void
test_not_aig_vector_random ()
{
  run_void_int_function_random (test_not_aig_vector,
                                AIG_VECTOR_TEST_NUM_RANDOM_TESTS);
}

void
test_not_aig_vector_releases ()
{
  AIGUniqueTable *table = NULL;
  AIGVector *aig_vector = NULL;
  AIGVector *result = NULL;
  int i = 0;
  init_error_management (stderr);
  init_memory_management ();
  aig_vector = create_aig_vector ();
  table = create_aig_unique_table (8);
  for (i = 0; i < 32; i++)
    {
      aig_vector->aig[i] = var_aig (&table, i + 1);
    }
  aig_vector->undefined = var_aig (&table, 33);
  result = not_aig_vector (&table, aig_vector);
  release_aig_vector (&table, result);
  release_aig_vector (&table, aig_vector);
  delete_aig_vector (result);
  delete_aig_vector (aig_vector);
  delete_aig_unique_table (table, b_false);
  finalise_memory_management ();
}

void
test_and_aig_vector (int int_x, int int_y)
{
  AIGVector *x = NULL;
  AIGVector *y = NULL;
  AIGVector *result = NULL;
  AIGUniqueTable *table = NULL;
  assert (sizeof (int) == 4);
  init_error_management (stderr);
  init_memory_management ();
  x = create_aig_vector ();
  y = create_aig_vector ();
  long_long_2_aig_vector (int_x, x);
  long_long_2_aig_vector (int_y, y);
  table = create_aig_unique_table (8);
  result = and_aig_vector (&table, x, y);
  if (aig_vector_2_long_long (result))
    {
      assert (int_x && int_y);
    }
  else
    {
      assert (!(int_x && int_y));
    }
  assert (result->undefined == AIG_FALSE);
  delete_aig_vector (result);
  delete_aig_vector (x);
  delete_aig_vector (y);
  delete_aig_unique_table (table, b_false);
  finalise_memory_management ();
}

void
test_and_aig_vector_1 ()
{
  test_and_aig_vector (0, INT_MIN);
}

void
test_and_aig_vector_2 ()
{
  test_and_aig_vector (INT_MIN, 0);
}

void
test_and_aig_vector_3 ()
{
  test_and_aig_vector (INT_MAX, 0);
}

void
test_and_aig_vector_4 ()
{
  test_and_aig_vector (0, INT_MAX);
}

void
test_and_aig_vector_5 ()
{
  test_and_aig_vector (0, 0);
}

void
test_and_aig_vector_undefined ()
{
  AIGVector *x = NULL;
  AIGVector *y = NULL;
  AIGVector *result = NULL;
  AIGUniqueTable *table = NULL;
  init_error_management (stderr);
  init_memory_management ();
  x = create_aig_vector ();
  y = create_aig_vector ();
  table = create_aig_unique_table (8);

  long_long_2_aig_vector (0, x);
  long_long_2_aig_vector (0, y);
  result = and_aig_vector (&table, x, y);
  assert (result->undefined == AIG_FALSE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = and_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_TRUE;
  result = and_aig_vector (&table, x, y);
  assert (result->undefined == AIG_FALSE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = and_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_FALSE;

  long_long_2_aig_vector (1, x);
  long_long_2_aig_vector (0, y);
  result = and_aig_vector (&table, x, y);
  assert (result->undefined == AIG_FALSE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = and_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_TRUE;
  result = and_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = and_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_FALSE;

  long_long_2_aig_vector (0, x);
  long_long_2_aig_vector (1, y);
  result = and_aig_vector (&table, x, y);
  assert (result->undefined == AIG_FALSE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = and_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_TRUE;
  result = and_aig_vector (&table, x, y);
  assert (result->undefined == AIG_FALSE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = and_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_FALSE;

  long_long_2_aig_vector (1, x);
  long_long_2_aig_vector (1, y);
  result = and_aig_vector (&table, x, y);
  assert (result->undefined == AIG_FALSE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = and_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_TRUE;
  result = and_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = and_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  delete_aig_vector (x);
  delete_aig_vector (y);
  delete_aig_unique_table (table, b_false);
  finalise_memory_management ();
}

void
test_and_aig_vector_random ()
{
  run_void_int_int_function_random (test_and_aig_vector,
                                    AIG_VECTOR_TEST_NUM_RANDOM_TESTS);
}

void
test_and_aig_vector_releases ()
{
  AIGVector *x = NULL;
  AIGVector *y = NULL;
  AIGVector *result = NULL;
  AIGUniqueTable *table = NULL;
  int i = 0;
  init_error_management (stderr);
  init_memory_management ();
  x = create_aig_vector ();
  y = create_aig_vector ();
  table = create_aig_unique_table (8);
  for (i = 0; i < 32; i++)
    {
      x->aig[i] = var_aig (&table, i + 1);
      y->aig[i] = var_aig (&table, i + 1 + 32);
    }
  x->undefined = var_aig (&table, 65);
  y->undefined = var_aig (&table, 66);
  result = and_aig_vector (&table, x, y);
  release_aig_vector (&table, result);
  release_aig_vector (&table, x);
  release_aig_vector (&table, y);
  delete_aig_vector (result);
  delete_aig_vector (x);
  delete_aig_vector (y);
  delete_aig_unique_table (table, b_false);
  finalise_memory_management ();
}

void
test_or_aig_vector (int int_x, int int_y)
{
  AIGVector *x = NULL;
  AIGVector *y = NULL;
  AIGVector *result = NULL;
  AIGUniqueTable *table = NULL;
  assert (sizeof (int) == 4);
  init_error_management (stderr);
  init_memory_management ();
  x = create_aig_vector ();
  y = create_aig_vector ();
  long_long_2_aig_vector (int_x, x);
  long_long_2_aig_vector (int_y, y);
  table = create_aig_unique_table (8);
  result = or_aig_vector (&table, x, y);
  if (aig_vector_2_long_long (result))
    {
      assert (int_x || int_y);
    }
  else
    {
      assert (!(int_x || int_y));
    }
  assert (result->undefined == AIG_FALSE);
  delete_aig_vector (result);
  delete_aig_vector (x);
  delete_aig_vector (y);
  delete_aig_unique_table (table, b_false);
  finalise_memory_management ();
}

void
test_or_aig_vector_1 ()
{
  test_or_aig_vector (0, INT_MIN);
}

void
test_or_aig_vector_2 ()
{
  test_or_aig_vector (INT_MIN, 0);
}

void
test_or_aig_vector_3 ()
{
  test_or_aig_vector (INT_MAX, 0);
}

void
test_or_aig_vector_4 ()
{
  test_or_aig_vector (0, INT_MAX);
}

void
test_or_aig_vector_5 ()
{
  test_or_aig_vector (0, 0);
}

void
test_or_aig_vector_undefined ()
{
  AIGVector *x = NULL;
  AIGVector *y = NULL;
  AIGVector *result = NULL;
  AIGUniqueTable *table = NULL;
  init_error_management (stderr);
  init_memory_management ();
  table = create_aig_unique_table (8);
  x = create_aig_vector ();
  y = create_aig_vector ();

  long_long_2_aig_vector (0, x);
  long_long_2_aig_vector (0, y);
  result = or_aig_vector (&table, x, y);
  assert (result->undefined == AIG_FALSE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = or_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_TRUE;
  result = or_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = or_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_FALSE;

  long_long_2_aig_vector (1, x);
  long_long_2_aig_vector (0, y);
  result = or_aig_vector (&table, x, y);
  assert (result->undefined == AIG_FALSE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = or_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_TRUE;
  result = or_aig_vector (&table, x, y);
  assert (result->undefined == AIG_FALSE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = or_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_FALSE;

  long_long_2_aig_vector (0, x);
  long_long_2_aig_vector (1, y);
  result = or_aig_vector (&table, x, y);
  assert (result->undefined == AIG_FALSE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = or_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_TRUE;
  result = or_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = or_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_FALSE;

  long_long_2_aig_vector (1, x);
  long_long_2_aig_vector (1, y);
  result = or_aig_vector (&table, x, y);
  assert (result->undefined == AIG_FALSE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = or_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_TRUE;
  result = or_aig_vector (&table, x, y);
  assert (result->undefined == AIG_FALSE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = or_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  delete_aig_vector (x);
  delete_aig_vector (y);
  delete_aig_unique_table (table, b_false);
  finalise_memory_management ();
}

void
test_or_aig_vector_random ()
{
  run_void_int_int_function_random (test_or_aig_vector,
                                    AIG_VECTOR_TEST_NUM_RANDOM_TESTS);
}

void
test_or_aig_vector_releases ()
{
  AIGVector *x = NULL;
  AIGVector *y = NULL;
  AIGVector *result = NULL;
  AIGUniqueTable *table = NULL;
  int i = 0;
  init_error_management (stderr);
  init_memory_management ();
  x = create_aig_vector ();
  y = create_aig_vector ();
  table = create_aig_unique_table (8);
  for (i = 0; i < 32; i++)
    {
      x->aig[i] = var_aig (&table, i + 1);
      y->aig[i] = var_aig (&table, i + 1 + 32);
    }
  x->undefined = var_aig (&table, 65);
  y->undefined = var_aig (&table, 66);
  result = or_aig_vector (&table, x, y);
  release_aig_vector (&table, result);
  release_aig_vector (&table, x);
  release_aig_vector (&table, y);
  delete_aig_vector (result);
  delete_aig_vector (x);
  delete_aig_vector (y);
  delete_aig_unique_table (table, b_false);
  finalise_memory_management ();
}

void
test_imp_aig_vector (int int_x, int int_y)
{
  AIGVector *x = NULL;
  AIGVector *y = NULL;
  AIGVector *result = NULL;
  AIGUniqueTable *table = NULL;
  assert (sizeof (int) == 4);
  init_error_management (stderr);
  init_memory_management ();
  x = create_aig_vector ();
  y = create_aig_vector ();
  long_long_2_aig_vector (int_x, x);
  long_long_2_aig_vector (int_y, y);
  table = create_aig_unique_table (8);
  result = imp_aig_vector (&table, x, y);
  if (aig_vector_2_long_long (result))
    {
      assert (!int_x || int_y);
    }
  else
    {
      assert (!(!int_x || int_y));
    }
  assert (result->undefined == AIG_FALSE);
  delete_aig_vector (result);
  delete_aig_vector (x);
  delete_aig_vector (y);
  delete_aig_unique_table (table, b_false);
  finalise_memory_management ();
}

void
test_imp_aig_vector_1 ()
{
  test_imp_aig_vector (0, INT_MIN);
}

void
test_imp_aig_vector_2 ()
{
  test_imp_aig_vector (INT_MIN, 0);
}

void
test_imp_aig_vector_3 ()
{
  test_imp_aig_vector (INT_MAX, 0);
}

void
test_imp_aig_vector_4 ()
{
  test_imp_aig_vector (0, INT_MAX);
}

void
test_imp_aig_vector_5 ()
{
  test_imp_aig_vector (0, 0);
}

void
test_imp_aig_vector_undefined ()
{
  AIGVector *x = NULL;
  AIGVector *y = NULL;
  AIGVector *result = NULL;
  AIGUniqueTable *table = NULL;
  init_error_management (stderr);
  init_memory_management ();
  table = create_aig_unique_table (8);
  x = create_aig_vector ();
  y = create_aig_vector ();

  long_long_2_aig_vector (0, x);
  long_long_2_aig_vector (0, y);
  result = imp_aig_vector (&table, x, y);
  assert (result->undefined == AIG_FALSE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = imp_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_TRUE;
  result = imp_aig_vector (&table, x, y);
  assert (result->undefined == AIG_FALSE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = imp_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_FALSE;

  long_long_2_aig_vector (1, x);
  long_long_2_aig_vector (0, y);
  result = imp_aig_vector (&table, x, y);
  assert (result->undefined == AIG_FALSE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = imp_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_TRUE;
  result = imp_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = imp_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_FALSE;

  long_long_2_aig_vector (0, x);
  long_long_2_aig_vector (1, y);
  result = imp_aig_vector (&table, x, y);
  assert (result->undefined == AIG_FALSE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = imp_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_TRUE;
  result = imp_aig_vector (&table, x, y);
  assert (result->undefined == AIG_FALSE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = imp_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_FALSE;

  long_long_2_aig_vector (1, x);
  long_long_2_aig_vector (1, y);
  result = imp_aig_vector (&table, x, y);
  assert (result->undefined == AIG_FALSE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = imp_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_TRUE;
  result = imp_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = imp_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  delete_aig_vector (x);
  delete_aig_vector (y);
  delete_aig_unique_table (table, b_false);
  finalise_memory_management ();
}

void
test_imp_aig_vector_random ()
{
  run_void_int_int_function_random (test_imp_aig_vector,
                                    AIG_VECTOR_TEST_NUM_RANDOM_TESTS);
}

void
test_imp_aig_vector_releases ()
{
  AIGVector *x = NULL;
  AIGVector *y = NULL;
  AIGVector *result = NULL;
  AIGUniqueTable *table = NULL;
  int i = 0;
  init_error_management (stderr);
  init_memory_management ();
  x = create_aig_vector ();
  y = create_aig_vector ();
  table = create_aig_unique_table (8);
  for (i = 0; i < 32; i++)
    {
      x->aig[i] = var_aig (&table, i + 1);
      y->aig[i] = var_aig (&table, i + 1 + 32);
    }
  x->undefined = var_aig (&table, 65);
  y->undefined = var_aig (&table, 66);
  result = imp_aig_vector (&table, x, y);
  release_aig_vector (&table, result);
  release_aig_vector (&table, x);
  release_aig_vector (&table, y);
  delete_aig_vector (result);
  delete_aig_vector (x);
  delete_aig_vector (y);
  delete_aig_unique_table (table, b_false);
  finalise_memory_management ();
}

void
test_dimp_aig_vector (int int_x, int int_y)
{
  AIGVector *x = NULL;
  AIGVector *y = NULL;
  AIGVector *result = NULL;
  AIGUniqueTable *table = NULL;
  assert (sizeof (int) == 4);
  init_error_management (stderr);
  init_memory_management ();
  x = create_aig_vector ();
  y = create_aig_vector ();
  long_long_2_aig_vector (int_x, x);
  long_long_2_aig_vector (int_y, y);
  table = create_aig_unique_table (8);
  result = dimp_aig_vector (&table, x, y);
  if (aig_vector_2_long_long (result))
    {
      assert ((!int_x || int_y) && (int_x || !int_y));
    }
  else
    {
      assert (!((!int_x || int_y) && (int_x || !int_y)));
    }
  assert (result->undefined == AIG_FALSE);
  delete_aig_vector (result);
  delete_aig_vector (x);
  delete_aig_vector (y);
  delete_aig_unique_table (table, b_false);
  finalise_memory_management ();
}

void
test_dimp_aig_vector_1 ()
{
  test_dimp_aig_vector (0, INT_MIN);
}

void
test_dimp_aig_vector_2 ()
{
  test_dimp_aig_vector (INT_MIN, 0);
}

void
test_dimp_aig_vector_3 ()
{
  test_dimp_aig_vector (INT_MAX, 0);
}

void
test_dimp_aig_vector_4 ()
{
  test_dimp_aig_vector (0, INT_MAX);
}

void
test_dimp_aig_vector_5 ()
{
  test_dimp_aig_vector (0, 0);
}

void
test_dimp_aig_vector_undefined ()
{
  AIGVector *x = NULL;
  AIGVector *y = NULL;
  AIGVector *result = NULL;
  AIGUniqueTable *table = NULL;
  init_error_management (stderr);
  init_memory_management ();
  table = create_aig_unique_table (8);
  x = create_aig_vector ();
  y = create_aig_vector ();

  long_long_2_aig_vector (0, x);
  long_long_2_aig_vector (0, y);
  result = dimp_aig_vector (&table, x, y);
  assert (result->undefined == AIG_FALSE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = dimp_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_TRUE;
  result = dimp_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = dimp_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_FALSE;

  long_long_2_aig_vector (1, x);
  long_long_2_aig_vector (0, y);
  result = dimp_aig_vector (&table, x, y);
  assert (result->undefined == AIG_FALSE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = dimp_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_TRUE;
  result = dimp_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = dimp_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_FALSE;

  long_long_2_aig_vector (0, x);
  long_long_2_aig_vector (1, y);
  result = dimp_aig_vector (&table, x, y);
  assert (result->undefined == AIG_FALSE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = dimp_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_TRUE;
  result = dimp_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = dimp_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_FALSE;

  long_long_2_aig_vector (1, x);
  long_long_2_aig_vector (1, y);
  result = dimp_aig_vector (&table, x, y);
  assert (result->undefined == AIG_FALSE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = dimp_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_TRUE;
  result = dimp_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = dimp_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  delete_aig_vector (x);
  delete_aig_vector (y);
  delete_aig_unique_table (table, b_false);
  finalise_memory_management ();
}

void
test_dimp_aig_vector_random ()
{
  run_void_int_int_function_random (test_dimp_aig_vector,
                                    AIG_VECTOR_TEST_NUM_RANDOM_TESTS);
}

void
test_dimp_aig_vector_releases ()
{
  AIGVector *x = NULL;
  AIGVector *y = NULL;
  AIGVector *result = NULL;
  AIGUniqueTable *table = NULL;
  int i = 0;
  init_error_management (stderr);
  init_memory_management ();
  x = create_aig_vector ();
  y = create_aig_vector ();
  table = create_aig_unique_table (8);
  for (i = 0; i < 32; i++)
    {
      x->aig[i] = var_aig (&table, i + 1);
      y->aig[i] = var_aig (&table, i + 1 + 32);
    }
  x->undefined = var_aig (&table, 65);
  y->undefined = var_aig (&table, 66);
  result = dimp_aig_vector (&table, x, y);
  release_aig_vector (&table, result);
  release_aig_vector (&table, x);
  release_aig_vector (&table, y);
  delete_aig_vector (result);
  delete_aig_vector (x);
  delete_aig_vector (y);
  delete_aig_unique_table (table, b_false);
  finalise_memory_management ();
}

void
test_invert_aig_vector (int x)
{
  AIGVector *result = NULL;
  init_error_management (stderr);
  init_memory_management ();
  result = create_aig_vector ();
  long_long_2_aig_vector (x, result);
  invert_aig_vector (result);
  assert (aig_vector_2_long_long (result) == ~x);
  assert (result->undefined == AIG_FALSE);
  delete_aig_vector (result);
  finalise_memory_management ();
}

void
test_invert_aig_vector_1 ()
{
  test_invert_aig_vector (INT_MAX);
}

void
test_invert_aig_vector_2 ()
{
  test_invert_aig_vector (INT_MIN);
}

void
test_invert_aig_vector_3 ()
{
  test_invert_aig_vector (0);
}

void
test_invert_aig_vector_4 ()
{
  test_invert_aig_vector (1);
}

void
test_invert_aig_vector_5 ()
{
  test_invert_aig_vector (-1);
}

void
test_invert_aig_vector_undefined ()
{
  AIGVector *aig_vector = NULL;
  init_error_management (stderr);
  init_memory_management ();
  aig_vector = create_aig_vector ();
  invert_aig_vector (aig_vector);
  assert (aig_vector->undefined == AIG_FALSE);
  delete_aig_vector (aig_vector);
  aig_vector = create_aig_vector ();
  aig_vector->undefined = AIG_TRUE;
  invert_aig_vector (aig_vector);
  assert (aig_vector->undefined == AIG_TRUE);
  delete_aig_vector (aig_vector);
  finalise_memory_management ();
}

void
test_invert_aig_vector_random ()
{
  run_void_int_function_random (test_invert_aig_vector,
                                AIG_VECTOR_TEST_NUM_RANDOM_TESTS);
}

void
test_invert_aig_vector_releases ()
{
  AIGUniqueTable *table = NULL;
  AIGVector *aig_vector = NULL;
  int i = 0;
  init_error_management (stderr);
  init_memory_management ();
  aig_vector = create_aig_vector ();
  table = create_aig_unique_table (8);
  for (i = 0; i < 32; i++)
    {
      aig_vector->aig[i] = var_aig (&table, i + 1);
    }
  aig_vector->undefined = var_aig (&table, 33);
  invert_aig_vector (aig_vector);
  release_aig_vector (&table, aig_vector);
  delete_aig_vector (aig_vector);
  delete_aig_unique_table (table, b_false);
  finalise_memory_management ();
}

void
test_band_aig_vector (int int_x, int int_y)
{
  AIGVector *x = NULL;
  AIGVector *y = NULL;
  AIGVector *result = NULL;
  AIGUniqueTable *table = NULL;
  assert (sizeof (int) == 4);
  init_error_management (stderr);
  init_memory_management ();
  x = create_aig_vector ();
  y = create_aig_vector ();
  long_long_2_aig_vector (int_x, x);
  long_long_2_aig_vector (int_y, y);
  table = create_aig_unique_table (8);
  result = band_aig_vector (&table, x, y);
  assert (aig_vector_2_long_long (result) == (int_x & int_y));
  assert (result->undefined == AIG_FALSE);
  delete_aig_vector (result);
  delete_aig_vector (x);
  delete_aig_vector (y);
  delete_aig_unique_table (table, b_false);
  finalise_memory_management ();
}

void
test_band_aig_vector_1 ()
{
  test_band_aig_vector (0, INT_MIN);
}

void
test_band_aig_vector_2 ()
{
  test_band_aig_vector (INT_MIN, 0);
}

void
test_band_aig_vector_3 ()
{
  test_band_aig_vector (INT_MAX, 0);
}

void
test_band_aig_vector_4 ()
{
  test_band_aig_vector (0, INT_MAX);
}

void
test_band_aig_vector_5 ()
{
  test_band_aig_vector (0, 0);
}

void
test_band_aig_vector_undefined ()
{
  AIGVector *x = NULL;
  AIGVector *y = NULL;
  AIGVector *result = NULL;
  AIGUniqueTable *table = NULL;
  init_error_management (stderr);
  init_memory_management ();
  table = create_aig_unique_table (8);
  x = create_aig_vector ();
  y = create_aig_vector ();

  long_long_2_aig_vector (0, x);
  long_long_2_aig_vector (0, y);
  result = band_aig_vector (&table, x, y);
  assert (result->undefined == AIG_FALSE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = band_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_TRUE;
  result = band_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = band_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  delete_aig_vector (x);
  delete_aig_vector (y);
  delete_aig_unique_table (table, b_false);
  finalise_memory_management ();
}

void
test_band_aig_vector_random ()
{
  run_void_int_int_function_random (test_band_aig_vector,
                                    AIG_VECTOR_TEST_NUM_RANDOM_TESTS);
}

void
test_band_aig_vector_releases ()
{
  AIGVector *x = NULL;
  AIGVector *y = NULL;
  AIGVector *result = NULL;
  AIGUniqueTable *table = NULL;
  int i = 0;
  init_error_management (stderr);
  init_memory_management ();
  x = create_aig_vector ();
  y = create_aig_vector ();
  table = create_aig_unique_table (8);
  for (i = 0; i < 32; i++)
    {
      x->aig[i] = var_aig (&table, i + 1);
      y->aig[i] = var_aig (&table, i + 1 + 32);
    }
  x->undefined = var_aig (&table, 65);
  y->undefined = var_aig (&table, 66);
  result = band_aig_vector (&table, x, y);
  release_aig_vector (&table, result);
  release_aig_vector (&table, x);
  release_aig_vector (&table, y);
  delete_aig_vector (result);
  delete_aig_vector (x);
  delete_aig_vector (y);
  delete_aig_unique_table (table, b_false);
  finalise_memory_management ();
}

void
test_bor_aig_vector (int int_x, int int_y)
{
  AIGVector *x = NULL;
  AIGVector *y = NULL;
  AIGVector *result = NULL;
  AIGUniqueTable *table = NULL;
  assert (sizeof (int) == 4);
  init_error_management (stderr);
  init_memory_management ();
  x = create_aig_vector ();
  y = create_aig_vector ();
  long_long_2_aig_vector (int_x, x);
  long_long_2_aig_vector (int_y, y);
  table = create_aig_unique_table (8);
  result = bor_aig_vector (&table, x, y);
  assert (aig_vector_2_long_long (result) == (int_x | int_y));
  assert (result->undefined == AIG_FALSE);
  delete_aig_vector (result);
  delete_aig_vector (x);
  delete_aig_vector (y);
  delete_aig_unique_table (table, b_false);
  finalise_memory_management ();
}

void
test_bor_aig_vector_1 ()
{
  test_bor_aig_vector (0, INT_MIN);
}

void
test_bor_aig_vector_2 ()
{
  test_bor_aig_vector (INT_MIN, 0);
}

void
test_bor_aig_vector_3 ()
{
  test_bor_aig_vector (INT_MAX, 0);
}

void
test_bor_aig_vector_4 ()
{
  test_bor_aig_vector (0, INT_MAX);
}

void
test_bor_aig_vector_5 ()
{
  test_bor_aig_vector (0, 0);
}

void
test_bor_aig_vector_undefined ()
{
  AIGVector *x = NULL;
  AIGVector *y = NULL;
  AIGVector *result = NULL;
  AIGUniqueTable *table = NULL;
  init_error_management (stderr);
  init_memory_management ();
  table = create_aig_unique_table (8);
  x = create_aig_vector ();
  y = create_aig_vector ();

  long_long_2_aig_vector (0, x);
  long_long_2_aig_vector (0, y);
  result = bor_aig_vector (&table, x, y);
  assert (result->undefined == AIG_FALSE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = bor_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_TRUE;
  result = bor_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = bor_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  delete_aig_vector (x);
  delete_aig_vector (y);
  delete_aig_unique_table (table, b_false);
  finalise_memory_management ();
}

void
test_bor_aig_vector_random ()
{
  run_void_int_int_function_random (test_bor_aig_vector,
                                    AIG_VECTOR_TEST_NUM_RANDOM_TESTS);
}

void
test_bor_aig_vector_releases ()
{
  AIGVector *x = NULL;
  AIGVector *y = NULL;
  AIGVector *result = NULL;
  AIGUniqueTable *table = NULL;
  int i = 0;
  init_error_management (stderr);
  init_memory_management ();
  x = create_aig_vector ();
  y = create_aig_vector ();
  table = create_aig_unique_table (8);
  for (i = 0; i < 32; i++)
    {
      x->aig[i] = var_aig (&table, i + 1);
      y->aig[i] = var_aig (&table, i + 1 + 32);
    }
  x->undefined = var_aig (&table, 65);
  y->undefined = var_aig (&table, 66);
  result = bor_aig_vector (&table, x, y);
  release_aig_vector (&table, result);
  release_aig_vector (&table, x);
  release_aig_vector (&table, y);
  delete_aig_vector (result);
  delete_aig_vector (x);
  delete_aig_vector (y);
  delete_aig_unique_table (table, b_false);
  finalise_memory_management ();
}

void
test_bxor_aig_vector (int int_x, int int_y)
{
  AIGVector *x = NULL;
  AIGVector *y = NULL;
  AIGVector *result = NULL;
  AIGUniqueTable *table = NULL;
  assert (sizeof (int) == 4);
  init_error_management (stderr);
  init_memory_management ();
  x = create_aig_vector ();
  y = create_aig_vector ();
  long_long_2_aig_vector (int_x, x);
  long_long_2_aig_vector (int_y, y);
  table = create_aig_unique_table (8);
  result = bxor_aig_vector (&table, x, y);
  assert (aig_vector_2_long_long (result) == (int_x ^ int_y));
  assert (result->undefined == AIG_FALSE);
  delete_aig_vector (result);
  delete_aig_vector (x);
  delete_aig_vector (y);
  delete_aig_unique_table (table, b_false);
  finalise_memory_management ();
}

void
test_bxor_aig_vector_1 ()
{
  test_bxor_aig_vector (0, INT_MIN);
}

void
test_bxor_aig_vector_2 ()
{
  test_bxor_aig_vector (INT_MIN, 0);
}

void
test_bxor_aig_vector_3 ()
{
  test_bxor_aig_vector (INT_MAX, 0);
}

void
test_bxor_aig_vector_4 ()
{
  test_bxor_aig_vector (0, INT_MAX);
}

void
test_bxor_aig_vector_5 ()
{
  test_bxor_aig_vector (0, 0);
}

void
test_bxor_aig_vector_undefined ()
{
  AIGVector *x = NULL;
  AIGVector *y = NULL;
  AIGVector *result = NULL;
  AIGUniqueTable *table = NULL;
  init_error_management (stderr);
  init_memory_management ();
  table = create_aig_unique_table (8);
  x = create_aig_vector ();
  y = create_aig_vector ();

  long_long_2_aig_vector (0, x);
  long_long_2_aig_vector (0, y);
  result = bxor_aig_vector (&table, x, y);
  assert (result->undefined == AIG_FALSE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = bxor_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_TRUE;
  result = bxor_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = bxor_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  delete_aig_vector (x);
  delete_aig_vector (y);
  delete_aig_unique_table (table, b_false);
  finalise_memory_management ();
}

void
test_bxor_aig_vector_random ()
{
  run_void_int_int_function_random (test_bxor_aig_vector,
                                    AIG_VECTOR_TEST_NUM_RANDOM_TESTS);
}

void
test_bxor_aig_vector_releases ()
{
  AIGVector *x = NULL;
  AIGVector *y = NULL;
  AIGVector *result = NULL;
  AIGUniqueTable *table = NULL;
  int i = 0;
  init_error_management (stderr);
  init_memory_management ();
  x = create_aig_vector ();
  y = create_aig_vector ();
  table = create_aig_unique_table (8);
  for (i = 0; i < 32; i++)
    {
      x->aig[i] = var_aig (&table, i + 1);
      y->aig[i] = var_aig (&table, i + 1 + 32);
    }
  x->undefined = var_aig (&table, 65);
  y->undefined = var_aig (&table, 66);
  result = bxor_aig_vector (&table, x, y);
  release_aig_vector (&table, result);
  release_aig_vector (&table, x);
  release_aig_vector (&table, y);
  delete_aig_vector (result);
  delete_aig_vector (x);
  delete_aig_vector (y);
  delete_aig_unique_table (table, b_false);
  finalise_memory_management ();
}

void
test_add_aig_vector (int int_x, int int_y)
{
  AIGVector *x = NULL;
  AIGVector *y = NULL;
  AIGVector *result = NULL;
  AIGUniqueTable *table = NULL;
  assert (!ext_allow_overflow);
  init_error_management (stderr);
  init_memory_management ();
  x = create_aig_vector ();
  y = create_aig_vector ();
  long_long_2_aig_vector (int_x, x);
  long_long_2_aig_vector (int_y, y);
  table = create_aig_unique_table (8);
  result = add_aig_vector (&table, x, y);
  if ((x->aig[31] == y->aig[31]) && (result->aig[31] != x->aig[31]))
    {
      assert (aig_vector_2_long_long (result) ==
              add_special_operator (int_x, int_y, 32));
      assert (result->undefined == AIG_TRUE);
    }
  else
    {
      assert (aig_vector_2_long_long (result) == int_x + int_y);
      assert (result->undefined == AIG_FALSE);
    }
  delete_aig_vector (result);
  delete_aig_vector (x);
  delete_aig_vector (y);
  delete_aig_unique_table (table, b_false);
  finalise_memory_management ();
}

void
test_add_aig_vector_1 ()
{
  test_add_aig_vector (INT_MIN, INT_MIN);
}

void
test_add_aig_vector_2 ()
{
  test_add_aig_vector (INT_MIN, INT_MAX);
}

void
test_add_aig_vector_3 ()
{
  test_add_aig_vector (INT_MAX, INT_MIN);
}

void
test_add_aig_vector_4 ()
{
  test_add_aig_vector (INT_MAX, INT_MAX);
}

void
test_add_aig_vector_5 ()
{
  test_add_aig_vector (INT_MAX, 0);
}

void
test_add_aig_vector_undefined ()
{
  AIGVector *x = NULL;
  AIGVector *y = NULL;
  AIGVector *result = NULL;
  AIGUniqueTable *table = NULL;
  assert (!ext_allow_overflow);
  init_error_management (stderr);
  init_memory_management ();
  table = create_aig_unique_table (8);
  x = create_aig_vector ();
  y = create_aig_vector ();

  long_long_2_aig_vector (0, x);
  long_long_2_aig_vector (0, y);
  result = add_aig_vector (&table, x, y);
  assert (result->undefined == AIG_FALSE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = add_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_TRUE;
  result = add_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = add_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_FALSE;

  long_long_2_aig_vector (INT_MIN, x);
  long_long_2_aig_vector (INT_MIN, y);
  result = add_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = add_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_TRUE;
  result = add_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = add_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_FALSE;

  long_long_2_aig_vector (INT_MIN, x);
  long_long_2_aig_vector (INT_MAX, y);
  result = add_aig_vector (&table, x, y);
  assert (result->undefined == AIG_FALSE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = add_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_TRUE;
  result = add_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = add_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_FALSE;

  long_long_2_aig_vector (INT_MAX, x);
  long_long_2_aig_vector (INT_MIN, y);
  result = add_aig_vector (&table, x, y);
  assert (result->undefined == AIG_FALSE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = add_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_TRUE;
  result = add_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = add_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_FALSE;

  long_long_2_aig_vector (INT_MAX, x);
  long_long_2_aig_vector (INT_MAX, y);
  result = add_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = add_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_TRUE;
  result = add_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = add_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_FALSE;

  long_long_2_aig_vector (INT_MIN, x);
  long_long_2_aig_vector (-1, y);
  result = add_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = add_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_TRUE;
  result = add_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = add_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_FALSE;

  long_long_2_aig_vector (-1, x);
  long_long_2_aig_vector (INT_MIN, y);
  result = add_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = add_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_TRUE;
  result = add_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = add_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_FALSE;

  long_long_2_aig_vector (0, x);
  long_long_2_aig_vector (INT_MIN, y);
  result = add_aig_vector (&table, x, y);
  assert (result->undefined == AIG_FALSE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = add_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_TRUE;
  result = add_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = add_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_FALSE;

  ext_allow_overflow = b_true;

  long_long_2_aig_vector (INT_MIN, x);
  long_long_2_aig_vector (INT_MIN, y);
  result = add_aig_vector (&table, x, y);
  assert (result->undefined == AIG_FALSE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = add_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_TRUE;
  result = add_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = add_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_FALSE;

  long_long_2_aig_vector (INT_MIN, x);
  long_long_2_aig_vector (INT_MAX, y);
  result = add_aig_vector (&table, x, y);
  assert (result->undefined == AIG_FALSE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = add_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_TRUE;
  result = add_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = add_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_FALSE;

  long_long_2_aig_vector (INT_MAX, x);
  long_long_2_aig_vector (INT_MIN, y);
  result = add_aig_vector (&table, x, y);
  assert (result->undefined == AIG_FALSE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = add_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_TRUE;
  result = add_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = add_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_FALSE;

  long_long_2_aig_vector (INT_MAX, x);
  long_long_2_aig_vector (INT_MAX, y);
  result = add_aig_vector (&table, x, y);
  assert (result->undefined == AIG_FALSE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = add_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_TRUE;
  result = add_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = add_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_FALSE;

  long_long_2_aig_vector (INT_MIN, x);
  long_long_2_aig_vector (-1, y);
  result = add_aig_vector (&table, x, y);
  assert (result->undefined == AIG_FALSE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = add_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_TRUE;
  result = add_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = add_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_FALSE;

  long_long_2_aig_vector (-1, x);
  long_long_2_aig_vector (INT_MIN, y);
  result = add_aig_vector (&table, x, y);
  assert (result->undefined == AIG_FALSE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = add_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_TRUE;
  result = add_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = add_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_FALSE;

  long_long_2_aig_vector (0, x);
  long_long_2_aig_vector (INT_MIN, y);
  result = add_aig_vector (&table, x, y);
  assert (result->undefined == AIG_FALSE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = add_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_TRUE;
  result = add_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = add_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  delete_aig_vector (x);
  delete_aig_vector (y);
  delete_aig_unique_table (table, b_false);
  finalise_memory_management ();
  ext_allow_overflow = b_false;
}

void
test_add_aig_vector_random ()
{
  run_void_int_int_function_random (test_add_aig_vector,
                                    AIG_VECTOR_TEST_NUM_RANDOM_TESTS);
}

void
test_add_aig_vector_releases ()
{
  AIGVector *x = NULL;
  AIGVector *y = NULL;
  AIGVector *result = NULL;
  AIGUniqueTable *table = NULL;
  int i = 0;
  init_error_management (stderr);
  init_memory_management ();
  assert (!ext_allow_overflow);
  x = create_aig_vector ();
  y = create_aig_vector ();
  table = create_aig_unique_table (8);
  for (i = 0; i < 32; i++)
    {
      x->aig[i] = var_aig (&table, i + 1);
      y->aig[i] = var_aig (&table, i + 1 + 32);
    }
  x->undefined = var_aig (&table, 65);
  y->undefined = var_aig (&table, 66);
  result = add_aig_vector (&table, x, y);
  release_aig_vector (&table, result);
  release_aig_vector (&table, x);
  release_aig_vector (&table, y);
  delete_aig_vector (result);
  delete_aig_vector (x);
  delete_aig_vector (y);
  delete_aig_unique_table (table, b_false);
  ext_allow_overflow = b_true;
  x = create_aig_vector ();
  y = create_aig_vector ();
  table = create_aig_unique_table (8);
  for (i = 0; i < 32; i++)
    {
      x->aig[i] = var_aig (&table, i + 1);
      y->aig[i] = var_aig (&table, i + 1 + 32);
    }
  x->undefined = var_aig (&table, 65);
  y->undefined = var_aig (&table, 66);
  result = add_aig_vector (&table, x, y);
  release_aig_vector (&table, result);
  release_aig_vector (&table, x);
  release_aig_vector (&table, y);
  delete_aig_vector (result);
  delete_aig_vector (x);
  delete_aig_vector (y);
  delete_aig_unique_table (table, b_false);
  finalise_memory_management ();
  ext_allow_overflow = b_false;
}

void
test_unary_minus_aig_vector (int x)
{
  AIGVector *aig_vector = NULL;
  AIGVector *result = NULL;
  AIGUniqueTable *table = NULL;
  assert (!ext_allow_overflow);
  init_error_management (stderr);
  init_memory_management ();
  aig_vector = create_aig_vector ();
  table = create_aig_unique_table (8);
  long_long_2_aig_vector (x, aig_vector);
  result = unary_minus_aig_vector (&table, aig_vector);
  if (x == INT_MIN)
    {
      assert (aig_vector_2_long_long (result) == INT_MIN);
      assert (result->undefined == AIG_TRUE);
    }
  else
    {
      assert (aig_vector_2_long_long (result) == -x);
      assert (result->undefined == AIG_FALSE);
    }
  delete_aig_vector (result);
  delete_aig_vector (aig_vector);
  delete_aig_unique_table (table, b_false);
  finalise_memory_management ();
}

void
test_unary_minus_aig_vector_1 ()
{
  test_unary_minus_aig_vector (INT_MAX);
}

void
test_unary_minus_aig_vector_2 ()
{
  test_unary_minus_aig_vector (INT_MIN);
}

void
test_unary_minus_aig_vector_3 ()
{
  test_unary_minus_aig_vector (0);
}

void
test_unary_minus_aig_vector_4 ()
{
  test_unary_minus_aig_vector (1);
}

void
test_unary_minus_aig_vector_5 ()
{
  test_unary_minus_aig_vector (-1);
}

void
test_unary_minus_aig_vector_undefined ()
{
  AIGVector *aig_vector = NULL;
  AIGVector *result = NULL;
  AIGUniqueTable *table = NULL;
  assert (!ext_allow_overflow);
  init_error_management (stderr);
  init_memory_management ();
  table = create_aig_unique_table (8);
  aig_vector = create_aig_vector ();

  long_long_2_aig_vector (0, aig_vector);
  result = unary_minus_aig_vector (&table, aig_vector);
  assert (result->undefined == AIG_FALSE);
  delete_aig_vector (result);
  aig_vector->undefined = AIG_TRUE;
  result = unary_minus_aig_vector (&table, aig_vector);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  aig_vector->undefined = AIG_FALSE;

  long_long_2_aig_vector (INT_MIN, aig_vector);
  result = unary_minus_aig_vector (&table, aig_vector);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  aig_vector->undefined = AIG_TRUE;
  result = unary_minus_aig_vector (&table, aig_vector);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  aig_vector->undefined = AIG_FALSE;

  long_long_2_aig_vector (INT_MAX, aig_vector);
  result = unary_minus_aig_vector (&table, aig_vector);
  assert (result->undefined == AIG_FALSE);
  delete_aig_vector (result);
  aig_vector->undefined = AIG_TRUE;
  result = unary_minus_aig_vector (&table, aig_vector);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  aig_vector->undefined = AIG_FALSE;

  ext_allow_overflow = b_true;

  long_long_2_aig_vector (0, aig_vector);
  result = unary_minus_aig_vector (&table, aig_vector);
  assert (result->undefined == AIG_FALSE);
  delete_aig_vector (result);
  aig_vector->undefined = AIG_TRUE;
  result = unary_minus_aig_vector (&table, aig_vector);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  aig_vector->undefined = AIG_FALSE;

  long_long_2_aig_vector (INT_MIN, aig_vector);
  result = unary_minus_aig_vector (&table, aig_vector);
  assert (result->undefined == AIG_FALSE);
  delete_aig_vector (result);
  aig_vector->undefined = AIG_TRUE;
  result = unary_minus_aig_vector (&table, aig_vector);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  aig_vector->undefined = AIG_FALSE;

  long_long_2_aig_vector (INT_MAX, aig_vector);
  result = unary_minus_aig_vector (&table, aig_vector);
  assert (result->undefined == AIG_FALSE);
  delete_aig_vector (result);
  aig_vector->undefined = AIG_TRUE;
  result = unary_minus_aig_vector (&table, aig_vector);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  delete_aig_vector (aig_vector);
  delete_aig_unique_table (table, b_false);
  finalise_memory_management ();
  ext_allow_overflow = b_false;
}


void
test_unary_minus_aig_vector_random ()
{
  run_void_int_function_random (test_unary_minus_aig_vector,
                                AIG_VECTOR_TEST_NUM_RANDOM_TESTS);
}

void
test_unary_minus_aig_vector_releases ()
{
  AIGVector *aig_vector = NULL;
  AIGVector *result = NULL;
  AIGUniqueTable *table = NULL;
  int i = 0;
  init_error_management (stderr);
  init_memory_management ();
  aig_vector = create_aig_vector ();
  table = create_aig_unique_table (8);
  for (i = 0; i < 32; i++)
    {
      aig_vector->aig[i] = var_aig (&table, i + 1);
    }
  aig_vector->undefined = var_aig (&table, 33);
  result = unary_minus_aig_vector (&table, aig_vector);
  release_aig_vector (&table, result);
  release_aig_vector (&table, aig_vector);
  delete_aig_vector (result);
  delete_aig_vector (aig_vector);
  delete_aig_unique_table (table, b_false);
  finalise_memory_management ();
}

void
test_subtract_aig_vector (int int_x, int int_y)
{
  AIGVector *x = NULL;
  AIGVector *y = NULL;
  AIGVector *comp = NULL;
  AIGVector *result = NULL;
  AIGUniqueTable *table = NULL;
  assert (!ext_allow_overflow);
  init_error_management (stderr);
  init_memory_management ();
  x = create_aig_vector ();
  y = create_aig_vector ();
  long_long_2_aig_vector (int_x, x);
  long_long_2_aig_vector (int_y, y);
  table = create_aig_unique_table (8);
  comp = unary_minus_aig_vector (&table, y);
  result = subtract_aig_vector (&table, x, y);
  if (((x->aig[31] == comp->aig[31]) && (result->aig[31] != x->aig[31])
       && (int_y != INT_MIN)) || ((int_x >= 0) && (int_y == INT_MIN)))
    {
      assert (aig_vector_2_long_long (result) ==
              subtract_special_operator (int_x, int_y, 32));
      assert (result->undefined == AIG_TRUE);
    }
  else
    {
      assert (aig_vector_2_long_long (result) == int_x - int_y);
      assert (result->undefined == AIG_FALSE);
    }
  release_aig_vector (&table, comp);
  delete_aig_vector (result);
  delete_aig_vector (x);
  delete_aig_vector (y);
  delete_aig_vector (comp);
  delete_aig_unique_table (table, b_false);
  finalise_memory_management ();
}

void
test_subtract_aig_vector_1 ()
{
  test_subtract_aig_vector (INT_MIN, INT_MIN);
}

void
test_subtract_aig_vector_2 ()
{
  test_subtract_aig_vector (INT_MIN, INT_MAX);
}

void
test_subtract_aig_vector_3 ()
{
  test_subtract_aig_vector (INT_MAX, INT_MIN);
}

void
test_subtract_aig_vector_4 ()
{
  test_subtract_aig_vector (INT_MAX, INT_MAX);
}

void
test_subtract_aig_vector_5 ()
{
  test_subtract_aig_vector (INT_MAX, 0);
}

void
test_subtract_aig_vector_undefined ()
{
  AIGVector *x = NULL;
  AIGVector *y = NULL;
  AIGVector *result = NULL;
  AIGUniqueTable *table = NULL;
  assert (!ext_allow_overflow);
  init_error_management (stderr);
  init_memory_management ();
  table = create_aig_unique_table (8);
  x = create_aig_vector ();
  y = create_aig_vector ();

  long_long_2_aig_vector (0, x);
  long_long_2_aig_vector (0, y);
  result = subtract_aig_vector (&table, x, y);
  assert (result->undefined == AIG_FALSE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = subtract_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_TRUE;
  result = subtract_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = subtract_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_FALSE;

  long_long_2_aig_vector (0, x);
  long_long_2_aig_vector (INT_MIN, y);
  result = subtract_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = subtract_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_TRUE;
  result = subtract_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = subtract_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_FALSE;

  long_long_2_aig_vector (INT_MIN, x);
  long_long_2_aig_vector (0, y);
  result = subtract_aig_vector (&table, x, y);
  assert (result->undefined == AIG_FALSE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = subtract_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_TRUE;
  result = subtract_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = subtract_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_FALSE;

  long_long_2_aig_vector (INT_MIN, x);
  long_long_2_aig_vector (INT_MIN, y);
  result = subtract_aig_vector (&table, x, y);
  assert (result->undefined == AIG_FALSE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = subtract_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_TRUE;
  result = subtract_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = subtract_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_FALSE;

  long_long_2_aig_vector (INT_MIN, x);
  long_long_2_aig_vector (INT_MAX, y);
  result = subtract_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = subtract_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_TRUE;
  result = subtract_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = subtract_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_FALSE;

  long_long_2_aig_vector (INT_MAX, x);
  long_long_2_aig_vector (INT_MIN, y);
  result = subtract_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = subtract_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_TRUE;
  result = subtract_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = subtract_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_FALSE;

  long_long_2_aig_vector (INT_MAX, x);
  long_long_2_aig_vector (INT_MAX, y);
  result = subtract_aig_vector (&table, x, y);
  assert (result->undefined == AIG_FALSE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = subtract_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_TRUE;
  result = subtract_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = subtract_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_FALSE;

  long_long_2_aig_vector (INT_MIN, x);
  long_long_2_aig_vector (1, y);
  result = subtract_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = subtract_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_TRUE;
  result = subtract_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = subtract_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_FALSE;

  ext_allow_overflow = b_true;

  long_long_2_aig_vector (0, x);
  long_long_2_aig_vector (0, y);
  result = subtract_aig_vector (&table, x, y);
  assert (result->undefined == AIG_FALSE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = subtract_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_TRUE;
  result = subtract_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = subtract_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_FALSE;

  long_long_2_aig_vector (0, x);
  long_long_2_aig_vector (INT_MIN, y);
  result = subtract_aig_vector (&table, x, y);
  assert (result->undefined == AIG_FALSE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = subtract_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_TRUE;
  result = subtract_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = subtract_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_FALSE;

  long_long_2_aig_vector (INT_MIN, x);
  long_long_2_aig_vector (0, y);
  result = subtract_aig_vector (&table, x, y);
  assert (result->undefined == AIG_FALSE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = subtract_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_TRUE;
  result = subtract_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = subtract_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_FALSE;

  long_long_2_aig_vector (INT_MIN, x);
  long_long_2_aig_vector (INT_MIN, y);
  result = subtract_aig_vector (&table, x, y);
  assert (result->undefined == AIG_FALSE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = subtract_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_TRUE;
  result = subtract_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = subtract_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_FALSE;

  long_long_2_aig_vector (INT_MIN, x);
  long_long_2_aig_vector (INT_MAX, y);
  result = subtract_aig_vector (&table, x, y);
  assert (result->undefined == AIG_FALSE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = subtract_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_TRUE;
  result = subtract_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = subtract_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_FALSE;

  long_long_2_aig_vector (INT_MAX, x);
  long_long_2_aig_vector (INT_MIN, y);
  result = subtract_aig_vector (&table, x, y);
  assert (result->undefined == AIG_FALSE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = subtract_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_TRUE;
  result = subtract_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = subtract_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_FALSE;

  long_long_2_aig_vector (INT_MAX, x);
  long_long_2_aig_vector (INT_MAX, y);
  result = subtract_aig_vector (&table, x, y);
  assert (result->undefined == AIG_FALSE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = subtract_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_TRUE;
  result = subtract_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = subtract_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_FALSE;

  long_long_2_aig_vector (INT_MIN, x);
  long_long_2_aig_vector (1, y);
  result = subtract_aig_vector (&table, x, y);
  assert (result->undefined == AIG_FALSE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = subtract_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_TRUE;
  result = subtract_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = subtract_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  delete_aig_vector (x);
  delete_aig_vector (y);
  delete_aig_unique_table (table, b_false);
  finalise_memory_management ();
  ext_allow_overflow = b_false;
}

void
test_subtract_aig_vector_random ()
{
  run_void_int_int_function_random (test_subtract_aig_vector,
                                    AIG_VECTOR_TEST_NUM_RANDOM_TESTS);
}

void
test_subtract_aig_vector_releases ()
{
  AIGVector *x = NULL;
  AIGVector *y = NULL;
  AIGVector *result = NULL;
  AIGUniqueTable *table = NULL;
  int i = 0;
  init_error_management (stderr);
  init_memory_management ();
  x = create_aig_vector ();
  y = create_aig_vector ();
  table = create_aig_unique_table (8);
  for (i = 0; i < 32; i++)
    {
      x->aig[i] = var_aig (&table, i + 1);
      y->aig[i] = var_aig (&table, i + 1 + 32);
    }
  x->undefined = var_aig (&table, 65);
  y->undefined = var_aig (&table, 66);
  result = subtract_aig_vector (&table, x, y);
  release_aig_vector (&table, result);
  release_aig_vector (&table, x);
  release_aig_vector (&table, y);
  delete_aig_vector (result);
  delete_aig_vector (x);
  delete_aig_vector (y);
  delete_aig_unique_table (table, b_false);
  finalise_memory_management ();
}

void
test_eq_aig_vector (int int_x, int int_y)
{
  AIGVector *x = NULL;
  AIGVector *y = NULL;
  AIGVector *result = NULL;
  AIGUniqueTable *table = NULL;
  init_error_management (stderr);
  init_memory_management ();
  x = create_aig_vector ();
  y = create_aig_vector ();
  long_long_2_aig_vector (int_x, x);
  long_long_2_aig_vector (int_y, y);
  table = create_aig_unique_table (8);
  result = eq_aig_vector (&table, x, y);
  if (int_x == int_y)
    {
      assert (aig_vector_2_long_long (result) == 1);
    }
  else
    {
      assert (aig_vector_2_long_long (result) == 0);
    }
  assert (result->undefined == AIG_FALSE);
  delete_aig_vector (result);
  delete_aig_vector (x);
  delete_aig_vector (y);
  delete_aig_unique_table (table, b_false);
  finalise_memory_management ();
}

void
test_eq_aig_vector_1 ()
{
  test_eq_aig_vector (0, 0);
}

void
test_eq_aig_vector_2 ()
{
  test_eq_aig_vector (INT_MIN, 0);
}

void
test_eq_aig_vector_3 ()
{
  test_eq_aig_vector (INT_MIN, INT_MAX);
}

void
test_eq_aig_vector_4 ()
{
  test_eq_aig_vector (INT_MAX, INT_MIN);
}

void
test_eq_aig_vector_5 ()
{
  test_eq_aig_vector (INT_MAX, -1);
}

void
test_eq_aig_vector_undefined ()
{
  AIGVector *x = NULL;
  AIGVector *y = NULL;
  AIGVector *result = NULL;
  AIGUniqueTable *table = NULL;
  init_error_management (stderr);
  init_memory_management ();
  table = create_aig_unique_table (8);
  x = create_aig_vector ();
  y = create_aig_vector ();

  long_long_2_aig_vector (0, x);
  long_long_2_aig_vector (0, y);
  result = eq_aig_vector (&table, x, y);
  assert (result->undefined == AIG_FALSE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = eq_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_TRUE;
  result = eq_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = eq_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  delete_aig_vector (x);
  delete_aig_vector (y);
  delete_aig_unique_table (table, b_false);
  finalise_memory_management ();
}

void
test_eq_aig_vector_random ()
{
  run_void_int_int_function_random (test_eq_aig_vector,
                                    AIG_VECTOR_TEST_NUM_RANDOM_TESTS);
}

void
test_eq_aig_vector_releases ()
{
  AIGVector *x = NULL;
  AIGVector *y = NULL;
  AIGVector *result = NULL;
  AIGUniqueTable *table = NULL;
  int i = 0;
  init_error_management (stderr);
  init_memory_management ();
  x = create_aig_vector ();
  y = create_aig_vector ();
  table = create_aig_unique_table (8);
  for (i = 0; i < 32; i++)
    {
      x->aig[i] = var_aig (&table, i + 1);
      y->aig[i] = var_aig (&table, i + 1 + 32);
    }
  x->undefined = var_aig (&table, 65);
  y->undefined = var_aig (&table, 66);
  result = eq_aig_vector (&table, x, y);
  release_aig_vector (&table, result);
  release_aig_vector (&table, x);
  release_aig_vector (&table, y);
  delete_aig_vector (result);
  delete_aig_vector (x);
  delete_aig_vector (y);
  delete_aig_unique_table (table, b_false);
  finalise_memory_management ();
}

void
test_neq_aig_vector (int int_x, int int_y)
{
  AIGVector *x = NULL;
  AIGVector *y = NULL;
  AIGVector *result = NULL;
  AIGUniqueTable *table = NULL;
  init_error_management (stderr);
  init_memory_management ();
  x = create_aig_vector ();
  y = create_aig_vector ();
  long_long_2_aig_vector (int_x, x);
  long_long_2_aig_vector (int_y, y);
  table = create_aig_unique_table (8);
  result = neq_aig_vector (&table, x, y);
  if (int_x != int_y)
    {
      assert (aig_vector_2_long_long (result) == 1);
    }
  else
    {
      assert (aig_vector_2_long_long (result) == 0);
    }
  assert (result->undefined == AIG_FALSE);
  delete_aig_vector (result);
  delete_aig_vector (x);
  delete_aig_vector (y);
  delete_aig_unique_table (table, b_false);
  finalise_memory_management ();
}

void
test_neq_aig_vector_1 ()
{
  test_neq_aig_vector (0, 0);
}

void
test_neq_aig_vector_2 ()
{
  test_neq_aig_vector (INT_MIN, 0);
}

void
test_neq_aig_vector_3 ()
{
  test_neq_aig_vector (INT_MIN, INT_MAX);
}

void
test_neq_aig_vector_4 ()
{
  test_neq_aig_vector (INT_MAX, INT_MIN);
}

void
test_neq_aig_vector_5 ()
{
  test_neq_aig_vector (INT_MAX, -1);
}

void
test_neq_aig_vector_undefined ()
{
  AIGVector *x = NULL;
  AIGVector *y = NULL;
  AIGVector *result = NULL;
  AIGUniqueTable *table = NULL;
  init_error_management (stderr);
  init_memory_management ();
  table = create_aig_unique_table (8);
  x = create_aig_vector ();
  y = create_aig_vector ();

  long_long_2_aig_vector (0, x);
  long_long_2_aig_vector (0, y);
  result = neq_aig_vector (&table, x, y);
  assert (result->undefined == AIG_FALSE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = neq_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_TRUE;
  result = neq_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = neq_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  delete_aig_vector (x);
  delete_aig_vector (y);
  delete_aig_unique_table (table, b_false);
  finalise_memory_management ();
}

void
test_neq_aig_vector_random ()
{
  run_void_int_int_function_random (test_neq_aig_vector,
                                    AIG_VECTOR_TEST_NUM_RANDOM_TESTS);
}

void
test_neq_aig_vector_releases ()
{
  AIGVector *x = NULL;
  AIGVector *y = NULL;
  AIGVector *result = NULL;
  AIGUniqueTable *table = NULL;
  int i = 0;
  init_error_management (stderr);
  init_memory_management ();
  x = create_aig_vector ();
  y = create_aig_vector ();
  table = create_aig_unique_table (8);
  for (i = 0; i < 32; i++)
    {
      x->aig[i] = var_aig (&table, i + 1);
      y->aig[i] = var_aig (&table, i + 1 + 32);
    }
  x->undefined = var_aig (&table, 65);
  y->undefined = var_aig (&table, 66);
  result = neq_aig_vector (&table, x, y);
  release_aig_vector (&table, result);
  release_aig_vector (&table, x);
  release_aig_vector (&table, y);
  delete_aig_vector (result);
  delete_aig_vector (x);
  delete_aig_vector (y);
  delete_aig_unique_table (table, b_false);
  finalise_memory_management ();
}

void
test_less_than_aig_vector (int int_x, int int_y)
{
  AIGVector *x = NULL;
  AIGVector *y = NULL;
  AIGVector *result = NULL;
  AIGUniqueTable *table = NULL;
  init_error_management (stderr);
  init_memory_management ();
  x = create_aig_vector ();
  y = create_aig_vector ();
  long_long_2_aig_vector (int_x, x);
  long_long_2_aig_vector (int_y, y);
  table = create_aig_unique_table (8);
  result = less_than_aig_vector (&table, x, y);
  if (int_x < int_y)
    {
      assert (aig_vector_2_long_long (result) == 1);
    }
  else
    {
      assert (aig_vector_2_long_long (result) == 0);
    }
  assert (result->undefined == AIG_FALSE);
  delete_aig_vector (result);
  delete_aig_vector (x);
  delete_aig_vector (y);
  delete_aig_unique_table (table, b_false);
  finalise_memory_management ();
}

void
test_less_than_aig_vector_1 ()
{
  test_less_than_aig_vector (0, 0);
}

void
test_less_than_aig_vector_2 ()
{
  test_less_than_aig_vector (INT_MIN, 0);
}

void
test_less_than_aig_vector_3 ()
{
  test_less_than_aig_vector (INT_MIN, INT_MAX);
}

void
test_less_than_aig_vector_4 ()
{
  test_less_than_aig_vector (INT_MAX, INT_MIN);
}

void
test_less_than_aig_vector_5 ()
{
  test_less_than_aig_vector (INT_MAX, -1);
}

void
test_less_than_aig_vector_undefined ()
{
  AIGVector *x = NULL;
  AIGVector *y = NULL;
  AIGVector *result = NULL;
  AIGUniqueTable *table = NULL;
  init_error_management (stderr);
  init_memory_management ();
  table = create_aig_unique_table (8);
  x = create_aig_vector ();
  y = create_aig_vector ();

  long_long_2_aig_vector (0, x);
  long_long_2_aig_vector (0, y);
  result = less_than_aig_vector (&table, x, y);
  assert (result->undefined == AIG_FALSE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = less_than_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_TRUE;
  result = less_than_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = less_than_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  delete_aig_vector (x);
  delete_aig_vector (y);
  delete_aig_unique_table (table, b_false);
  finalise_memory_management ();
}

void
test_less_than_aig_vector_random ()
{
  run_void_int_int_function_random (test_less_than_aig_vector,
                                    AIG_VECTOR_TEST_NUM_RANDOM_TESTS);
}

void
test_less_than_aig_vector_releases ()
{
  AIGVector *x = NULL;
  AIGVector *y = NULL;
  AIGVector *result = NULL;
  AIGUniqueTable *table = NULL;
  int i = 0;
  init_error_management (stderr);
  init_memory_management ();
  x = create_aig_vector ();
  y = create_aig_vector ();
  table = create_aig_unique_table (8);
  for (i = 0; i < 32; i++)
    {
      x->aig[i] = var_aig (&table, i + 1);
      y->aig[i] = var_aig (&table, i + 32 + 1);
    }
  x->undefined = var_aig (&table, 65);
  y->undefined = var_aig (&table, 66);
  result = less_than_aig_vector (&table, x, y);
  release_aig_vector (&table, result);
  release_aig_vector (&table, x);
  release_aig_vector (&table, y);
  delete_aig_vector (result);
  delete_aig_vector (x);
  delete_aig_vector (y);
  delete_aig_unique_table (table, b_false);
  finalise_memory_management ();
}

void
test_less_than_or_equal_aig_vector (int int_x, int int_y)
{
  AIGVector *x = NULL;
  AIGVector *y = NULL;
  AIGVector *result = NULL;
  AIGUniqueTable *table = NULL;
  init_error_management (stderr);
  init_memory_management ();
  x = create_aig_vector ();
  y = create_aig_vector ();
  long_long_2_aig_vector (int_x, x);
  long_long_2_aig_vector (int_y, y);
  table = create_aig_unique_table (8);
  result = less_than_or_equal_aig_vector (&table, x, y);
  if (int_x <= int_y)
    {
      assert (aig_vector_2_long_long (result) == 1);
    }
  else
    {
      assert (aig_vector_2_long_long (result) == 0);
    }
  assert (result->undefined == AIG_FALSE);
  delete_aig_vector (result);
  delete_aig_vector (x);
  delete_aig_vector (y);
  delete_aig_unique_table (table, b_false);
  finalise_memory_management ();
}

void
test_less_than_or_equal_aig_vector_1 ()
{
  test_less_than_or_equal_aig_vector (0, 0);
}

void
test_less_than_or_equal_aig_vector_2 ()
{
  test_less_than_or_equal_aig_vector (INT_MIN, 0);
}

void
test_less_than_or_equal_aig_vector_3 ()
{
  test_less_than_or_equal_aig_vector (INT_MIN, INT_MAX);
}

void
test_less_than_or_equal_aig_vector_4 ()
{
  test_less_than_or_equal_aig_vector (INT_MAX, INT_MIN);
}

void
test_less_than_or_equal_aig_vector_5 ()
{
  test_less_than_or_equal_aig_vector (INT_MAX, -1);
}

void
test_less_than_or_equal_aig_vector_undefined ()
{
  AIGVector *x = NULL;
  AIGVector *y = NULL;
  AIGVector *result = NULL;
  AIGUniqueTable *table = NULL;
  init_error_management (stderr);
  init_memory_management ();
  table = create_aig_unique_table (8);
  x = create_aig_vector ();
  y = create_aig_vector ();

  long_long_2_aig_vector (0, x);
  long_long_2_aig_vector (0, y);
  result = less_than_or_equal_aig_vector (&table, x, y);
  assert (result->undefined == AIG_FALSE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = less_than_or_equal_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_TRUE;
  result = less_than_or_equal_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = less_than_or_equal_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  delete_aig_vector (x);
  delete_aig_vector (y);
  delete_aig_unique_table (table, b_false);
  finalise_memory_management ();
}

void
test_less_than_or_equal_aig_vector_random ()
{
  run_void_int_int_function_random (test_less_than_or_equal_aig_vector,
                                    AIG_VECTOR_TEST_NUM_RANDOM_TESTS);
}

void
test_less_than_or_equal_aig_vector_releases ()
{
  AIGVector *x = NULL;
  AIGVector *y = NULL;
  AIGVector *result = NULL;
  AIGUniqueTable *table = NULL;
  int i = 0;
  init_error_management (stderr);
  init_memory_management ();
  x = create_aig_vector ();
  y = create_aig_vector ();
  table = create_aig_unique_table (8);
  for (i = 0; i < 32; i++)
    {
      x->aig[i] = var_aig (&table, i + 1);
      y->aig[i] = var_aig (&table, i + 32 + 1);
    }
  x->undefined = var_aig (&table, 65);
  y->undefined = var_aig (&table, 66);
  result = less_than_or_equal_aig_vector (&table, x, y);
  release_aig_vector (&table, result);
  release_aig_vector (&table, x);
  release_aig_vector (&table, y);
  delete_aig_vector (result);
  delete_aig_vector (x);
  delete_aig_vector (y);
  delete_aig_unique_table (table, b_false);
  finalise_memory_management ();
}

void
test_greater_than_aig_vector (int int_x, int int_y)
{
  AIGVector *x = NULL;
  AIGVector *y = NULL;
  AIGVector *result = NULL;
  AIGUniqueTable *table = NULL;
  init_error_management (stderr);
  init_memory_management ();
  x = create_aig_vector ();
  y = create_aig_vector ();
  long_long_2_aig_vector (int_x, x);
  long_long_2_aig_vector (int_y, y);
  table = create_aig_unique_table (8);
  result = greater_than_aig_vector (&table, x, y);
  if (int_x > int_y)
    {
      assert (aig_vector_2_long_long (result) == 1);
    }
  else
    {
      assert (aig_vector_2_long_long (result) == 0);
    }
  assert (result->undefined == AIG_FALSE);
  delete_aig_vector (result);
  delete_aig_vector (x);
  delete_aig_vector (y);
  delete_aig_unique_table (table, b_false);
  finalise_memory_management ();
}

void
test_greater_than_aig_vector_1 ()
{
  test_greater_than_aig_vector (0, 0);
}

void
test_greater_than_aig_vector_2 ()
{
  test_greater_than_aig_vector (INT_MIN, 0);
}

void
test_greater_than_aig_vector_3 ()
{
  test_greater_than_aig_vector (INT_MIN, INT_MAX);
}

void
test_greater_than_aig_vector_4 ()
{
  test_greater_than_aig_vector (INT_MAX, INT_MIN);
}

void
test_greater_than_aig_vector_5 ()
{
  test_greater_than_aig_vector (INT_MAX, -1);
}

void
test_greater_than_aig_vector_undefined ()
{
  AIGVector *x = NULL;
  AIGVector *y = NULL;
  AIGVector *result = NULL;
  AIGUniqueTable *table = NULL;
  init_error_management (stderr);
  init_memory_management ();
  table = create_aig_unique_table (8);
  x = create_aig_vector ();
  y = create_aig_vector ();

  long_long_2_aig_vector (0, x);
  long_long_2_aig_vector (0, y);
  result = greater_than_aig_vector (&table, x, y);
  assert (result->undefined == AIG_FALSE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = greater_than_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_TRUE;
  result = greater_than_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = greater_than_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  delete_aig_vector (x);
  delete_aig_vector (y);
  delete_aig_unique_table (table, b_false);
  finalise_memory_management ();
}

void
test_greater_than_aig_vector_random ()
{
  run_void_int_int_function_random (test_greater_than_aig_vector,
                                    AIG_VECTOR_TEST_NUM_RANDOM_TESTS);
}

void
test_greater_than_aig_vector_releases ()
{
  AIGVector *x = NULL;
  AIGVector *y = NULL;
  AIGVector *result = NULL;
  AIGUniqueTable *table = NULL;
  int i = 0;
  init_error_management (stderr);
  init_memory_management ();
  x = create_aig_vector ();
  y = create_aig_vector ();
  table = create_aig_unique_table (8);
  for (i = 0; i < 32; i++)
    {
      x->aig[i] = var_aig (&table, i + 1);
      y->aig[i] = var_aig (&table, i + 32 + 1);
    }
  x->undefined = var_aig (&table, 65);
  y->undefined = var_aig (&table, 66);
  result = greater_than_aig_vector (&table, x, y);
  release_aig_vector (&table, result);
  release_aig_vector (&table, x);
  release_aig_vector (&table, y);
  delete_aig_vector (result);
  delete_aig_vector (x);
  delete_aig_vector (y);
  delete_aig_unique_table (table, b_false);
  finalise_memory_management ();
}

void
test_greater_than_or_equal_aig_vector (int int_x, int int_y)
{
  AIGVector *x = NULL;
  AIGVector *y = NULL;
  AIGVector *result = NULL;
  AIGUniqueTable *table = NULL;
  init_error_management (stderr);
  init_memory_management ();
  x = create_aig_vector ();
  y = create_aig_vector ();
  long_long_2_aig_vector (int_x, x);
  long_long_2_aig_vector (int_y, y);
  table = create_aig_unique_table (8);
  result = greater_than_or_equal_aig_vector (&table, x, y);
  if (int_x >= int_y)
    {
      assert (aig_vector_2_long_long (result) == 1);
    }
  else
    {
      assert (aig_vector_2_long_long (result) == 0);
    }
  assert (result->undefined == AIG_FALSE);
  delete_aig_vector (result);
  delete_aig_vector (x);
  delete_aig_vector (y);
  delete_aig_unique_table (table, b_false);
  finalise_memory_management ();
}

void
test_greater_than_or_equal_aig_vector_1 ()
{
  test_greater_than_or_equal_aig_vector (0, 0);
}

void
test_greater_than_or_equal_aig_vector_2 ()
{
  test_greater_than_or_equal_aig_vector (INT_MIN, 0);
}

void
test_greater_than_or_equal_aig_vector_3 ()
{
  test_greater_than_or_equal_aig_vector (INT_MIN, INT_MAX);
}

void
test_greater_than_or_equal_aig_vector_4 ()
{
  test_greater_than_or_equal_aig_vector (INT_MAX, INT_MIN);
}

void
test_greater_than_or_equal_aig_vector_5 ()
{
  test_greater_than_or_equal_aig_vector (INT_MAX, -1);
}

void
test_greater_than_or_equal_aig_vector_undefined ()
{
  AIGVector *x = NULL;
  AIGVector *y = NULL;
  AIGVector *result = NULL;
  AIGUniqueTable *table = NULL;
  init_error_management (stderr);
  init_memory_management ();
  table = create_aig_unique_table (8);
  x = create_aig_vector ();
  y = create_aig_vector ();

  long_long_2_aig_vector (0, x);
  long_long_2_aig_vector (0, y);
  result = greater_than_or_equal_aig_vector (&table, x, y);
  assert (result->undefined == AIG_FALSE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = greater_than_or_equal_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_TRUE;
  result = greater_than_or_equal_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = greater_than_or_equal_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  delete_aig_vector (x);
  delete_aig_vector (y);
  delete_aig_unique_table (table, b_false);
  finalise_memory_management ();
}

void
test_greater_than_or_equal_aig_vector_random ()
{
  run_void_int_int_function_random (test_greater_than_or_equal_aig_vector,
                                    AIG_VECTOR_TEST_NUM_RANDOM_TESTS);
}

void
test_greater_than_or_equal_aig_vector_releases ()
{
  AIGVector *x = NULL;
  AIGVector *y = NULL;
  AIGVector *result = NULL;
  AIGUniqueTable *table = NULL;
  int i = 0;
  init_error_management (stderr);
  init_memory_management ();
  x = create_aig_vector ();
  y = create_aig_vector ();
  table = create_aig_unique_table (8);
  for (i = 0; i < 32; i++)
    {
      x->aig[i] = var_aig (&table, i + 1);
      y->aig[i] = var_aig (&table, i + 32 + 1);
    }
  x->undefined = var_aig (&table, 65);
  y->undefined = var_aig (&table, 66);
  result = greater_than_or_equal_aig_vector (&table, x, y);
  release_aig_vector (&table, result);
  release_aig_vector (&table, x);
  release_aig_vector (&table, y);
  delete_aig_vector (result);
  delete_aig_vector (x);
  delete_aig_vector (y);
  delete_aig_unique_table (table, b_false);
  finalise_memory_management ();
}

void
test_shift_left_aig_vector (int int_x, int int_y)
{
  AIGUniqueTable *table = NULL;
  AIGVector *x = NULL;
  AIGVector *y = NULL;
  AIGVector *result = NULL;
  Bool no_overflow = b_true;
  int i = 0;
  assert (!ext_allow_overflow);
  init_error_management (stderr);
  init_memory_management ();
  table = create_aig_unique_table (8);
  x = create_aig_vector ();
  y = create_aig_vector ();
  long_long_2_aig_vector (int_x, x);
  long_long_2_aig_vector (int_y, y);
  result = shift_left_aig_vector (&table, x, y);
  if (int_y < 0 || int_y >= 32)
    {
      assert (aig_vector_2_long_long (result) ==
              shift_left_special_operator (int_x, int_y, 32));
      assert (result->undefined == AIG_TRUE);
    }
  else
    {
      for (i = 0; i < int_y; i++)
        {
          no_overflow = no_overflow && (x->aig[31] == x->aig[31 - i]);
        }
      if (no_overflow)
        {
          assert (aig_vector_2_long_long (result) == int_x << int_y);
          assert (result->undefined == AIG_FALSE);
        }
      else
        {
          assert (aig_vector_2_long_long (result) ==
                  shift_left_special_operator (int_x, int_y, 32));
          assert (result->undefined == AIG_TRUE);
        }
    }
  delete_aig_vector (result);
  delete_aig_vector (y);
  delete_aig_vector (x);
  delete_aig_unique_table (table, b_false);
  finalise_memory_management ();
}

void
test_shift_left_aig_vector_1 ()
{
  test_shift_left_aig_vector (INT_MIN, INT_MIN);
}

void
test_shift_left_aig_vector_2 ()
{
  test_shift_left_aig_vector (INT_MIN, INT_MAX);
}

void
test_shift_left_aig_vector_3 ()
{
  test_shift_left_aig_vector (INT_MAX, INT_MIN);
}

void
test_shift_left_aig_vector_4 ()
{
  test_shift_left_aig_vector (INT_MAX, INT_MAX);
}

void
test_shift_left_aig_vector_5 ()
{
  test_shift_left_aig_vector (INT_MAX, 0);
}

void
test_shift_left_aig_vector_undefined ()
{
  AIGUniqueTable *table = NULL;
  AIGVector *x = NULL;
  AIGVector *y = NULL;
  AIGVector *result = NULL;
  assert (!ext_allow_overflow);
  init_error_management (stderr);
  init_memory_management ();
  table = create_aig_unique_table (8);
  x = create_aig_vector ();
  y = create_aig_vector ();

  long_long_2_aig_vector (0, x);
  long_long_2_aig_vector (0, y);
  result = shift_left_aig_vector (&table, x, y);
  assert (result->undefined == AIG_FALSE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = shift_left_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_TRUE;
  result = shift_left_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = shift_left_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_FALSE;

  long_long_2_aig_vector (0, x);
  long_long_2_aig_vector (INT_MIN, y);
  result = shift_left_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = shift_left_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_TRUE;
  result = shift_left_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = shift_left_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_FALSE;

  long_long_2_aig_vector (INT_MAX, x);
  long_long_2_aig_vector (1, y);
  result = shift_left_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = shift_left_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_TRUE;
  result = shift_left_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = shift_left_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_FALSE;

  long_long_2_aig_vector (INT_MIN, x);
  long_long_2_aig_vector (1, y);
  result = shift_left_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = shift_left_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_TRUE;
  result = shift_left_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = shift_left_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_FALSE;

  long_long_2_aig_vector (1073741824, x);       /* 1073741824 == 2 ^ 30 */
  long_long_2_aig_vector (1, y);
  result = shift_left_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = shift_left_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_TRUE;
  result = shift_left_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = shift_left_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_FALSE;

  long_long_2_aig_vector (1073741824, x);
  long_long_2_aig_vector (2, y);
  result = shift_left_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = shift_left_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_TRUE;
  result = shift_left_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = shift_left_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_FALSE;

  long_long_2_aig_vector (1073741823, x);       /* 1073741823 == (2 ^ 30) - 1 */
  long_long_2_aig_vector (1, y);
  result = shift_left_aig_vector (&table, x, y);
  assert (result->undefined == AIG_FALSE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = shift_left_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_TRUE;
  result = shift_left_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = shift_left_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_FALSE;

  long_long_2_aig_vector (-1073741824, x);
  long_long_2_aig_vector (1, y);
  result = shift_left_aig_vector (&table, x, y);
  assert (result->undefined == AIG_FALSE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = shift_left_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_TRUE;
  result = shift_left_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = shift_left_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_FALSE;

  long_long_2_aig_vector (-1073741824, x);
  long_long_2_aig_vector (2, y);
  result = shift_left_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = shift_left_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_TRUE;
  result = shift_left_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = shift_left_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_FALSE;

  long_long_2_aig_vector (-1073741825, x);
  long_long_2_aig_vector (2, y);
  result = shift_left_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = shift_left_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_TRUE;
  result = shift_left_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = shift_left_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_FALSE;

  ext_allow_overflow = b_true;

  long_long_2_aig_vector (1073741824, x);
  long_long_2_aig_vector (2, y);
  result = shift_left_aig_vector (&table, x, y);
  assert (result->undefined == AIG_FALSE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = shift_left_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_TRUE;
  result = shift_left_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = shift_left_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_FALSE;

  long_long_2_aig_vector (1073741824, x);
  long_long_2_aig_vector (31, y);
  result = shift_left_aig_vector (&table, x, y);
  assert (result->undefined == AIG_FALSE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = shift_left_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_TRUE;
  result = shift_left_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = shift_left_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_FALSE;

  long_long_2_aig_vector (1073741824, x);
  long_long_2_aig_vector (32, y);
  result = shift_left_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = shift_left_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_TRUE;
  result = shift_left_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = shift_left_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_FALSE;

  long_long_2_aig_vector (1073741824, x);
  long_long_2_aig_vector (33, y);
  result = shift_left_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = shift_left_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_TRUE;
  result = shift_left_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = shift_left_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_FALSE;

  long_long_2_aig_vector (1073741824, x);
  long_long_2_aig_vector (-4, y);
  result = shift_left_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = shift_left_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_TRUE;
  result = shift_left_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = shift_left_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_FALSE;

  long_long_2_aig_vector (-1073741825, x);
  long_long_2_aig_vector (2, y);
  result = shift_left_aig_vector (&table, x, y);
  assert (result->undefined == AIG_FALSE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = shift_left_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_TRUE;
  result = shift_left_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = shift_left_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  delete_aig_vector (y);
  delete_aig_vector (x);
  delete_aig_unique_table (table, b_false);
  finalise_memory_management ();
  ext_allow_overflow = b_false;
}


void
test_shift_left_aig_vector_random ()
{
  run_void_int_int_function_random (test_shift_left_aig_vector,
                                    AIG_VECTOR_TEST_NUM_RANDOM_TESTS);
}

void
test_shift_left_aig_vector_releases ()
{
  AIGUniqueTable *table = NULL;
  AIGVector *x = NULL;
  AIGVector *y = NULL;
  AIGVector *result = NULL;
  int i = 0;
  assert (!ext_allow_overflow);
  init_error_management (stderr);
  init_memory_management ();
  table = create_aig_unique_table (8);
  x = create_aig_vector ();
  y = create_aig_vector ();
  for (i = 0; i < 32; i++)
    {
      x->aig[i] = var_aig (&table, i + 1);
      y->aig[i] = var_aig (&table, i + 32 + 1);
    }
  x->undefined = var_aig (&table, 65);
  y->undefined = var_aig (&table, 66);
  result = shift_left_aig_vector (&table, x, y);
  release_aig_vector (&table, result);
  release_aig_vector (&table, y);
  release_aig_vector (&table, x);
  delete_aig_vector (result);
  delete_aig_vector (y);
  delete_aig_vector (x);
  delete_aig_unique_table (table, b_false);
  ext_allow_overflow = b_true;
  table = create_aig_unique_table (8);
  x = create_aig_vector ();
  y = create_aig_vector ();
  for (i = 0; i < 32; i++)
    {
      x->aig[i] = var_aig (&table, i + 1);
      y->aig[i] = var_aig (&table, i + 32 + 1);
    }
  x->undefined = var_aig (&table, 65);
  y->undefined = var_aig (&table, 66);
  result = shift_left_aig_vector (&table, x, y);
  release_aig_vector (&table, result);
  release_aig_vector (&table, y);
  release_aig_vector (&table, x);
  delete_aig_vector (result);
  delete_aig_vector (y);
  delete_aig_vector (x);
  delete_aig_unique_table (table, b_false);
  finalise_memory_management ();
  ext_allow_overflow = b_false;
}

void
test_shift_right_aig_vector (int int_x, int int_y)
{
  AIGUniqueTable *table = NULL;
  AIGVector *x = NULL;
  AIGVector *y = NULL;
  AIGVector *result = NULL;
  init_error_management (stderr);
  init_memory_management ();
  table = create_aig_unique_table (8);
  x = create_aig_vector ();
  y = create_aig_vector ();
  long_long_2_aig_vector (int_x, x);
  long_long_2_aig_vector (int_y, y);
  result = shift_right_aig_vector (&table, x, y);
  if ((int_x < 0) || (int_y < 0) || (int_y >= 32))
    {
      assert (aig_vector_2_long_long (result) ==
              shift_right_special_operator (int_x, int_y, 32));
      assert (result->undefined == AIG_TRUE);
    }
  else
    {
      assert (aig_vector_2_long_long (result) == int_x >> int_y);
      assert (result->undefined == AIG_FALSE);
    }
  delete_aig_vector (result);
  delete_aig_vector (y);
  delete_aig_vector (x);
  delete_aig_unique_table (table, b_false);
  finalise_memory_management ();
}

void
test_shift_right_aig_vector_1 ()
{
  test_shift_right_aig_vector (INT_MIN, INT_MIN);
}

void
test_shift_right_aig_vector_2 ()
{
  test_shift_right_aig_vector (INT_MIN, INT_MAX);
}

void
test_shift_right_aig_vector_3 ()
{
  test_shift_right_aig_vector (INT_MAX, INT_MIN);
}

void
test_shift_right_aig_vector_4 ()
{
  test_shift_right_aig_vector (INT_MAX, INT_MAX);
}

void
test_shift_right_aig_vector_5 ()
{
  test_shift_right_aig_vector (INT_MAX, 0);
}

void
test_shift_right_aig_vector_undefined ()
{
  AIGUniqueTable *table = NULL;
  AIGVector *x = NULL;
  AIGVector *y = NULL;
  AIGVector *result = NULL;
  init_error_management (stderr);
  init_memory_management ();
  table = create_aig_unique_table (8);
  x = create_aig_vector ();
  y = create_aig_vector ();

  long_long_2_aig_vector (0, x);
  long_long_2_aig_vector (0, y);
  result = shift_right_aig_vector (&table, x, y);
  assert (result->undefined == AIG_FALSE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = shift_right_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_TRUE;
  result = shift_right_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = shift_right_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_FALSE;

  long_long_2_aig_vector (INT_MIN, x);
  long_long_2_aig_vector (0, y);
  result = shift_right_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = shift_right_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_TRUE;
  result = shift_right_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = shift_right_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_FALSE;

  long_long_2_aig_vector (0, x);
  long_long_2_aig_vector (INT_MIN, y);
  result = shift_right_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = shift_right_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_TRUE;
  result = shift_right_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = shift_right_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_FALSE;

  long_long_2_aig_vector (INT_MIN, x);
  long_long_2_aig_vector (INT_MIN, y);
  result = shift_right_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = shift_right_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_TRUE;
  result = shift_right_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = shift_right_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_FALSE;

  long_long_2_aig_vector (0, x);
  long_long_2_aig_vector (32, y);
  result = shift_right_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = shift_right_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_TRUE;
  result = shift_right_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = shift_right_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_FALSE;

  long_long_2_aig_vector (0, x);
  long_long_2_aig_vector (33, y);
  result = shift_right_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = shift_right_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_TRUE;
  result = shift_right_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = shift_right_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  delete_aig_vector (y);
  delete_aig_vector (x);
  delete_aig_unique_table (table, b_false);
  finalise_memory_management ();
}

void
test_shift_right_aig_vector_random ()
{
  run_void_int_int_function_random (test_shift_right_aig_vector,
                                    AIG_VECTOR_TEST_NUM_RANDOM_TESTS);
}

void
test_shift_right_aig_vector_releases ()
{
  AIGUniqueTable *table = NULL;
  AIGVector *x = NULL;
  AIGVector *y = NULL;
  AIGVector *result = NULL;
  int i = 0;
  init_error_management (stderr);
  init_memory_management ();
  table = create_aig_unique_table (8);
  x = create_aig_vector ();
  y = create_aig_vector ();
  for (i = 0; i < 32; i++)
    {
      x->aig[i] = var_aig (&table, i + 1);
      y->aig[i] = var_aig (&table, i + 32 + 1);
    }
  x->undefined = var_aig (&table, 65);
  y->undefined = var_aig (&table, 66);
  result = shift_right_aig_vector (&table, x, y);
  release_aig_vector (&table, result);
  release_aig_vector (&table, y);
  release_aig_vector (&table, x);
  delete_aig_vector (result);
  delete_aig_vector (y);
  delete_aig_vector (x);
  delete_aig_unique_table (table, b_false);
  finalise_memory_management ();
}

Bool
multiplication_overflow_32bit (int x, int y)
{
  int x_bits[32];
  int y_bits[32];
  int y_comp_bits[32];
  int result_bits_left[32];
  int result_bits_right[32];
  int additional_bit = 0;
  int temp_bits[32];
  int i = 0;
  int j = 0;
  const int number_of_bits = 32;
  Bool no_overflow = b_true;
  if (y == INT_MIN)
    {
      if ((x == 0) || (x == 1))
        {
          return b_false;
        }
      else
        {
          return b_true;
        }
    }
  long_long_2_bin_c32sat_math (x, x_bits, number_of_bits);
  long_long_2_bin_c32sat_math (y, y_bits, number_of_bits);
  long_long_2_bin_c32sat_math (-y, y_comp_bits, number_of_bits);
  for (i = 0; i < number_of_bits; i++)
    {
      result_bits_left[i] = 0;
      result_bits_right[i] = x_bits[i];
    }
  additional_bit = 0;
  /* booth multiplication  algorithm */
  for (i = 0; i < number_of_bits; i++)
    {
      if (result_bits_right[0] && !additional_bit)
        {
          binary_add_special_operator (result_bits_left, y_comp_bits,
                                       temp_bits, number_of_bits);
          for (j = 0; j < number_of_bits; j++)
            {
              result_bits_left[j] = temp_bits[j];
            }
        }
      else if (!result_bits_right[0] && additional_bit)
        {
          binary_add_special_operator (result_bits_left, y_bits, temp_bits,
                                       number_of_bits);
          for (j = 0; j < number_of_bits; j++)
            {
              result_bits_left[j] = temp_bits[j];
            }
        }
      /* shift */
      additional_bit = result_bits_right[0];
      for (j = 0; j < number_of_bits - 1; j++)
        {
          result_bits_right[j] = result_bits_right[j + 1];
        }
      result_bits_right[number_of_bits - 1] = result_bits_left[0];
      for (j = 0; j < number_of_bits - 1; j++)
        {
          result_bits_left[j] = result_bits_left[j + 1];
        }
    }
  no_overflow = b_true;
  for (i = 0; i < number_of_bits; i++)
    {
      no_overflow = no_overflow
        && (result_bits_left[i] == result_bits_right[number_of_bits - 1]);
    }
  return !no_overflow;
}

void
test_multiply_aig_vector (int int_x, int int_y)
{
  AIGUniqueTable *table = NULL;
  AIGVector *x = NULL;
  AIGVector *y = NULL;
  AIGVector *result = NULL;
  assert (!ext_allow_overflow);
  init_error_management (stderr);
  init_memory_management ();
  table = create_aig_unique_table (8);
  x = create_aig_vector ();
  y = create_aig_vector ();
  long_long_2_aig_vector (int_x, x);
  long_long_2_aig_vector (int_y, y);
  result = multiply_aig_vector (&table, x, y);
  if (multiplication_overflow_32bit (int_x, int_y))
    {
      assert (aig_vector_2_long_long (result) ==
              multiply_special_operator (int_x, int_y, 32));
      assert (result->undefined == AIG_TRUE);
    }
  else
    {
      assert (aig_vector_2_long_long (result) == int_x * int_y);
      assert (result->undefined == AIG_FALSE);
    }
  delete_aig_vector (result);
  delete_aig_vector (y);
  delete_aig_vector (x);
  delete_aig_unique_table (table, b_false);
  finalise_memory_management ();
}

void
test_multiply_aig_vector_1 ()
{
  test_multiply_aig_vector (INT_MIN, INT_MIN);
}

void
test_multiply_aig_vector_2 ()
{
  test_multiply_aig_vector (INT_MIN, INT_MAX);
}

void
test_multiply_aig_vector_3 ()
{
  test_multiply_aig_vector (INT_MAX, INT_MIN);
}

void
test_multiply_aig_vector_4 ()
{
  test_multiply_aig_vector (INT_MAX, INT_MAX);
}

void
test_multiply_aig_vector_5 ()
{
  test_multiply_aig_vector (INT_MIN, -1);
}

void
test_multiply_aig_vector_6 ()
{
  test_multiply_aig_vector (-1, INT_MIN);
}

void
test_multiply_aig_vector_7 ()
{
  test_multiply_aig_vector (INT_MAX, -1);
}

void
test_multiply_aig_vector_8 ()
{
  test_multiply_aig_vector (-1, INT_MAX);
}

void
test_multiply_aig_vector_9 ()
{
  test_multiply_aig_vector (-1, -1);
}

void
test_multiply_aig_vector_10 ()
{
  test_multiply_aig_vector (INT_MIN, 0);
}

void
test_multiply_aig_vector_11 ()
{
  test_multiply_aig_vector (0, INT_MIN);
}

void
test_multiply_aig_vector_12 ()
{
  test_multiply_aig_vector (INT_MAX, 0);
}

void
test_multiply_aig_vector_13 ()
{
  test_multiply_aig_vector (0, INT_MAX);
}

void
test_multiply_aig_vector_14 ()
{
  test_multiply_aig_vector (0, 0);
}

void
test_multiply_aig_vector_15 ()
{
  test_multiply_aig_vector (-1, 0);
}

void
test_multiply_aig_vector_16 ()
{
  test_multiply_aig_vector (0, -1);
}

void
test_multiply_aig_vector_17 ()
{
  test_multiply_aig_vector (300, 400);
}

void
test_multiply_aig_vector_18 ()
{
  test_multiply_aig_vector (300, -400);
}

void
test_multiply_aig_vector_19 ()
{
  test_multiply_aig_vector (-300, 400);
}

void
test_multiply_aig_vector_20 ()
{
  test_multiply_aig_vector (-300, -400);
}

void
test_multiply_aig_vector_21 ()
{
  test_multiply_aig_vector (1073741824, -2);
}

void
test_multiply_aig_vector_22 ()
{
  test_multiply_aig_vector (-1073741824, -2);
}

void
test_multiply_aig_vector_undefined ()
{
  AIGVector *x = NULL;
  AIGVector *y = NULL;
  AIGVector *result = NULL;
  AIGUniqueTable *table = NULL;
  assert (!ext_allow_overflow);
  init_error_management (stderr);
  init_memory_management ();
  table = create_aig_unique_table (8);
  x = create_aig_vector ();
  y = create_aig_vector ();

  long_long_2_aig_vector (0, x);
  long_long_2_aig_vector (0, y);
  result = multiply_aig_vector (&table, x, y);
  assert (result->undefined == AIG_FALSE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = multiply_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_TRUE;
  result = multiply_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = multiply_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_FALSE;

  long_long_2_aig_vector (INT_MIN, x);
  long_long_2_aig_vector (-1, y);
  result = multiply_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = multiply_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_TRUE;
  result = multiply_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = multiply_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_FALSE;

  long_long_2_aig_vector (INT_MIN, x);
  long_long_2_aig_vector (INT_MIN, y);
  result = multiply_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = multiply_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_TRUE;
  result = multiply_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = multiply_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_FALSE;

  long_long_2_aig_vector (INT_MIN, x);
  long_long_2_aig_vector (INT_MAX, y);
  result = multiply_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = multiply_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_TRUE;
  result = multiply_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = multiply_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_FALSE;

  long_long_2_aig_vector (INT_MAX, x);
  long_long_2_aig_vector (INT_MIN, y);
  result = multiply_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = multiply_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_TRUE;
  result = multiply_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = multiply_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_FALSE;

  long_long_2_aig_vector (INT_MAX, x);
  long_long_2_aig_vector (INT_MAX, y);
  result = multiply_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = multiply_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_TRUE;
  result = multiply_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = multiply_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_FALSE;

  long_long_2_aig_vector (-1073741824, x);
  long_long_2_aig_vector (2, y);
  result = multiply_aig_vector (&table, x, y);
  assert (result->undefined == AIG_FALSE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = multiply_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_TRUE;
  result = multiply_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = multiply_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_FALSE;

  long_long_2_aig_vector (-1073741825, x);
  long_long_2_aig_vector (2, y);
  result = multiply_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = multiply_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_TRUE;
  result = multiply_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = multiply_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_FALSE;

  long_long_2_aig_vector (-1, x);
  long_long_2_aig_vector (INT_MIN, y);
  result = multiply_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = multiply_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_TRUE;
  result = multiply_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = multiply_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_FALSE;

  long_long_2_aig_vector (65538, x);
  long_long_2_aig_vector (-65534, y);
  result = multiply_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = multiply_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_TRUE;
  result = multiply_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = multiply_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_FALSE;

  ext_allow_overflow = b_true;

  long_long_2_aig_vector (0, x);
  long_long_2_aig_vector (0, y);
  result = multiply_aig_vector (&table, x, y);
  assert (result->undefined == AIG_FALSE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = multiply_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_TRUE;
  result = multiply_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = multiply_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_FALSE;

  long_long_2_aig_vector (INT_MIN, x);
  long_long_2_aig_vector (-1, y);
  result = multiply_aig_vector (&table, x, y);
  assert (result->undefined == AIG_FALSE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = multiply_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_TRUE;
  result = multiply_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = multiply_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_FALSE;

  long_long_2_aig_vector (INT_MIN, x);
  long_long_2_aig_vector (INT_MIN, y);
  result = multiply_aig_vector (&table, x, y);
  assert (result->undefined == AIG_FALSE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = multiply_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_TRUE;
  result = multiply_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = multiply_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_FALSE;

  long_long_2_aig_vector (INT_MIN, x);
  long_long_2_aig_vector (INT_MAX, y);
  result = multiply_aig_vector (&table, x, y);
  assert (result->undefined == AIG_FALSE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = multiply_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_TRUE;
  result = multiply_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = multiply_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_FALSE;

  long_long_2_aig_vector (INT_MAX, x);
  long_long_2_aig_vector (INT_MIN, y);
  result = multiply_aig_vector (&table, x, y);
  assert (result->undefined == AIG_FALSE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = multiply_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_TRUE;
  result = multiply_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = multiply_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_FALSE;

  long_long_2_aig_vector (INT_MAX, x);
  long_long_2_aig_vector (INT_MAX, y);
  result = multiply_aig_vector (&table, x, y);
  assert (result->undefined == AIG_FALSE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = multiply_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_TRUE;
  result = multiply_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = multiply_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_FALSE;

  long_long_2_aig_vector (-1073741824, x);
  long_long_2_aig_vector (2, y);
  result = multiply_aig_vector (&table, x, y);
  assert (result->undefined == AIG_FALSE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = multiply_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_TRUE;
  result = multiply_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = multiply_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_FALSE;

  long_long_2_aig_vector (-1073741825, x);
  long_long_2_aig_vector (2, y);
  result = multiply_aig_vector (&table, x, y);
  assert (result->undefined == AIG_FALSE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = multiply_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_TRUE;
  result = multiply_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = multiply_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_FALSE;

  long_long_2_aig_vector (-1, x);
  long_long_2_aig_vector (INT_MIN, y);
  result = multiply_aig_vector (&table, x, y);
  assert (result->undefined == AIG_FALSE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = multiply_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_TRUE;
  result = multiply_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = multiply_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_FALSE;

  long_long_2_aig_vector (65538, x);
  long_long_2_aig_vector (-65534, y);
  result = multiply_aig_vector (&table, x, y);
  assert (result->undefined == AIG_FALSE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = multiply_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_TRUE;
  result = multiply_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = multiply_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  delete_aig_vector (x);
  delete_aig_vector (y);
  delete_aig_unique_table (table, b_false);
  finalise_memory_management ();
  ext_allow_overflow = b_false;
}

void
test_multiply_aig_vector_random ()
{
  run_void_int_int_function_random (test_multiply_aig_vector,
                                    AIG_VECTOR_TEST_NUM_RANDOM_TESTS);
}

void
test_multiply_aig_vector_releases ()
{
  AIGVector *x = NULL;
  AIGVector *y = NULL;
  AIGVector *result = NULL;
  AIGUniqueTable *table = NULL;
  int i = 0;
  assert (!ext_allow_overflow);
  init_error_management (stderr);
  init_memory_management ();
  assert (!ext_allow_overflow);
  x = create_aig_vector ();
  y = create_aig_vector ();
  table = create_aig_unique_table (8);
  for (i = 0; i < 32; i++)
    {
      x->aig[i] = var_aig (&table, i + 1);
      y->aig[i] = var_aig (&table, i + 32 + 1);
    }
  x->undefined = var_aig (&table, 65);
  y->undefined = var_aig (&table, 66);
  result = multiply_aig_vector (&table, x, y);
  release_aig_vector (&table, result);
  release_aig_vector (&table, x);
  release_aig_vector (&table, y);
  delete_aig_vector (result);
  delete_aig_vector (x);
  delete_aig_vector (y);
  delete_aig_unique_table (table, b_false);
  ext_allow_overflow = b_true;
  x = create_aig_vector ();
  y = create_aig_vector ();
  table = create_aig_unique_table (8);
  for (i = 0; i < 32; i++)
    {
      x->aig[i] = var_aig (&table, i + 1);
      y->aig[i] = var_aig (&table, i + 32 + 1);
    }
  x->undefined = var_aig (&table, 65);
  y->undefined = var_aig (&table, 66);
  result = multiply_aig_vector (&table, x, y);
  release_aig_vector (&table, result);
  release_aig_vector (&table, x);
  release_aig_vector (&table, y);
  delete_aig_vector (result);
  delete_aig_vector (x);
  delete_aig_vector (y);
  delete_aig_unique_table (table, b_false);
  finalise_memory_management ();
  ext_allow_overflow = b_false;
}

void
test_if_then_else_aig_vector (int int_x, int int_y, int int_z)
{
  AIGUniqueTable *table = NULL;
  AIGVector *x = NULL;
  AIGVector *y = NULL;
  AIGVector *z = NULL;
  AIGVector *result = NULL;
  init_error_management (stderr);
  init_memory_management ();
  table = create_aig_unique_table (8);
  x = create_aig_vector ();
  y = create_aig_vector ();
  z = create_aig_vector ();
  long_long_2_aig_vector (int_x, x);
  long_long_2_aig_vector (int_y, y);
  long_long_2_aig_vector (int_z, z);
  result = if_then_else_aig_vector (&table, x, y, z);
  assert (aig_vector_2_long_long (result) == (int_x ? int_y : int_z));
  assert (result->undefined == AIG_FALSE);
  delete_aig_vector (result);
  delete_aig_vector (y);
  delete_aig_vector (x);
  delete_aig_vector (z);
  delete_aig_unique_table (table, b_false);
  finalise_memory_management ();
}

void
test_if_then_else_aig_vector_1 ()
{
  test_if_then_else_aig_vector (0, 0, 0);
}

void
test_if_then_else_aig_vector_2 ()
{
  test_if_then_else_aig_vector (0, 0, INT_MAX);
}

void
test_if_then_else_aig_vector_3 ()
{
  test_if_then_else_aig_vector (0, INT_MAX, 0);
}

void
test_if_then_else_aig_vector_4 ()
{
  test_if_then_else_aig_vector (0, INT_MAX, INT_MAX);
}

void
test_if_then_else_aig_vector_5 ()
{
  test_if_then_else_aig_vector (INT_MAX, 0, 0);
}

void
test_if_then_else_aig_vector_6 ()
{
  test_if_then_else_aig_vector (INT_MAX, 0, INT_MAX);
}

void
test_if_then_else_aig_vector_7 ()
{
  test_if_then_else_aig_vector (INT_MAX, INT_MAX, 0);
}

void
test_if_then_else_aig_vector_8 ()
{
  test_if_then_else_aig_vector (INT_MAX, INT_MAX, INT_MAX);
}

void
test_if_then_else_aig_vector_undefined ()
{
  AIGVector *x = NULL;
  AIGVector *y = NULL;
  AIGVector *z = NULL;
  AIGVector *result = NULL;
  AIGUniqueTable *table = NULL;
  init_error_management (stderr);
  init_memory_management ();
  table = create_aig_unique_table (8);
  x = create_aig_vector ();
  y = create_aig_vector ();
  z = create_aig_vector ();

  long_long_2_aig_vector (0, x);
  long_long_2_aig_vector (0, y);
  long_long_2_aig_vector (0, z);
  result = if_then_else_aig_vector (&table, x, y, z);
  assert (result->undefined == AIG_FALSE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = if_then_else_aig_vector (&table, x, y, z);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_TRUE;
  result = if_then_else_aig_vector (&table, x, y, z);
  assert (result->undefined == AIG_FALSE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = if_then_else_aig_vector (&table, x, y, z);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_FALSE;
  z->undefined = AIG_TRUE;
  result = if_then_else_aig_vector (&table, x, y, z);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = if_then_else_aig_vector (&table, x, y, z);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_TRUE;
  result = if_then_else_aig_vector (&table, x, y, z);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = if_then_else_aig_vector (&table, x, y, z);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_FALSE;
  z->undefined = AIG_FALSE;

  long_long_2_aig_vector (0, x);
  long_long_2_aig_vector (0, y);
  long_long_2_aig_vector (1, z);
  result = if_then_else_aig_vector (&table, x, y, z);
  assert (result->undefined == AIG_FALSE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = if_then_else_aig_vector (&table, x, y, z);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_TRUE;
  result = if_then_else_aig_vector (&table, x, y, z);
  assert (result->undefined == AIG_FALSE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = if_then_else_aig_vector (&table, x, y, z);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_FALSE;
  z->undefined = AIG_TRUE;
  result = if_then_else_aig_vector (&table, x, y, z);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = if_then_else_aig_vector (&table, x, y, z);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_TRUE;
  result = if_then_else_aig_vector (&table, x, y, z);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = if_then_else_aig_vector (&table, x, y, z);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_FALSE;
  z->undefined = AIG_FALSE;

  long_long_2_aig_vector (0, x);
  long_long_2_aig_vector (1, y);
  long_long_2_aig_vector (0, z);
  result = if_then_else_aig_vector (&table, x, y, z);
  assert (result->undefined == AIG_FALSE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = if_then_else_aig_vector (&table, x, y, z);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_TRUE;
  result = if_then_else_aig_vector (&table, x, y, z);
  assert (result->undefined == AIG_FALSE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = if_then_else_aig_vector (&table, x, y, z);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_FALSE;
  z->undefined = AIG_TRUE;
  result = if_then_else_aig_vector (&table, x, y, z);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = if_then_else_aig_vector (&table, x, y, z);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_TRUE;
  result = if_then_else_aig_vector (&table, x, y, z);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = if_then_else_aig_vector (&table, x, y, z);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_FALSE;
  z->undefined = AIG_FALSE;

  long_long_2_aig_vector (0, x);
  long_long_2_aig_vector (1, y);
  long_long_2_aig_vector (1, z);
  result = if_then_else_aig_vector (&table, x, y, z);
  assert (result->undefined == AIG_FALSE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = if_then_else_aig_vector (&table, x, y, z);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_TRUE;
  result = if_then_else_aig_vector (&table, x, y, z);
  assert (result->undefined == AIG_FALSE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = if_then_else_aig_vector (&table, x, y, z);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_FALSE;
  z->undefined = AIG_TRUE;
  result = if_then_else_aig_vector (&table, x, y, z);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = if_then_else_aig_vector (&table, x, y, z);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_TRUE;
  result = if_then_else_aig_vector (&table, x, y, z);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = if_then_else_aig_vector (&table, x, y, z);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_FALSE;
  z->undefined = AIG_FALSE;

  long_long_2_aig_vector (1, x);
  long_long_2_aig_vector (0, y);
  long_long_2_aig_vector (0, z);
  result = if_then_else_aig_vector (&table, x, y, z);
  assert (result->undefined == AIG_FALSE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = if_then_else_aig_vector (&table, x, y, z);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_TRUE;
  result = if_then_else_aig_vector (&table, x, y, z);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = if_then_else_aig_vector (&table, x, y, z);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_FALSE;
  z->undefined = AIG_TRUE;
  result = if_then_else_aig_vector (&table, x, y, z);
  assert (result->undefined == AIG_FALSE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = if_then_else_aig_vector (&table, x, y, z);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_TRUE;
  result = if_then_else_aig_vector (&table, x, y, z);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = if_then_else_aig_vector (&table, x, y, z);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_FALSE;
  z->undefined = AIG_FALSE;

  long_long_2_aig_vector (1, x);
  long_long_2_aig_vector (0, y);
  long_long_2_aig_vector (1, z);
  result = if_then_else_aig_vector (&table, x, y, z);
  assert (result->undefined == AIG_FALSE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = if_then_else_aig_vector (&table, x, y, z);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_TRUE;
  result = if_then_else_aig_vector (&table, x, y, z);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = if_then_else_aig_vector (&table, x, y, z);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_FALSE;
  z->undefined = AIG_TRUE;
  result = if_then_else_aig_vector (&table, x, y, z);
  assert (result->undefined == AIG_FALSE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = if_then_else_aig_vector (&table, x, y, z);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_TRUE;
  result = if_then_else_aig_vector (&table, x, y, z);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = if_then_else_aig_vector (&table, x, y, z);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_FALSE;
  z->undefined = AIG_FALSE;

  long_long_2_aig_vector (1, x);
  long_long_2_aig_vector (1, y);
  long_long_2_aig_vector (0, z);
  result = if_then_else_aig_vector (&table, x, y, z);
  assert (result->undefined == AIG_FALSE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = if_then_else_aig_vector (&table, x, y, z);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_TRUE;
  result = if_then_else_aig_vector (&table, x, y, z);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = if_then_else_aig_vector (&table, x, y, z);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_FALSE;
  z->undefined = AIG_TRUE;
  result = if_then_else_aig_vector (&table, x, y, z);
  assert (result->undefined == AIG_FALSE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = if_then_else_aig_vector (&table, x, y, z);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_TRUE;
  result = if_then_else_aig_vector (&table, x, y, z);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = if_then_else_aig_vector (&table, x, y, z);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_FALSE;
  z->undefined = AIG_FALSE;

  long_long_2_aig_vector (1, x);
  long_long_2_aig_vector (1, y);
  long_long_2_aig_vector (1, z);
  result = if_then_else_aig_vector (&table, x, y, z);
  assert (result->undefined == AIG_FALSE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = if_then_else_aig_vector (&table, x, y, z);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_TRUE;
  result = if_then_else_aig_vector (&table, x, y, z);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = if_then_else_aig_vector (&table, x, y, z);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_FALSE;
  z->undefined = AIG_TRUE;
  result = if_then_else_aig_vector (&table, x, y, z);
  assert (result->undefined == AIG_FALSE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = if_then_else_aig_vector (&table, x, y, z);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_TRUE;
  result = if_then_else_aig_vector (&table, x, y, z);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = if_then_else_aig_vector (&table, x, y, z);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  delete_aig_vector (x);
  delete_aig_vector (y);
  delete_aig_vector (z);
  delete_aig_unique_table (table, b_false);
  finalise_memory_management ();
}

void
test_if_then_else_aig_vector_random ()
{
  run_void_int_int_int_function_random (test_if_then_else_aig_vector,
                                        AIG_VECTOR_TEST_NUM_RANDOM_TESTS);
}

void
test_if_then_else_aig_vector_releases ()
{
  AIGVector *x = NULL;
  AIGVector *y = NULL;
  AIGVector *z = NULL;
  AIGVector *result = NULL;
  AIGUniqueTable *table = NULL;
  int i = 0;
  init_error_management (stderr);
  init_memory_management ();
  x = create_aig_vector ();
  y = create_aig_vector ();
  z = create_aig_vector ();
  table = create_aig_unique_table (8);
  for (i = 0; i < 32; i++)
    {
      x->aig[i] = var_aig (&table, i + 1);
      y->aig[i] = var_aig (&table, i + 32 + 1);
      z->aig[i] = var_aig (&table, i + 64 + 1);
    }
  x->undefined = var_aig (&table, 97);
  y->undefined = var_aig (&table, 98);
  z->undefined = var_aig (&table, 99);
  result = if_then_else_aig_vector (&table, x, y, z);
  release_aig_vector (&table, result);
  release_aig_vector (&table, x);
  release_aig_vector (&table, y);
  release_aig_vector (&table, z);
  delete_aig_vector (result);
  delete_aig_vector (x);
  delete_aig_vector (y);
  delete_aig_vector (z);
  delete_aig_unique_table (table, b_false);
  finalise_memory_management ();
}

void
test_divide_aig_vector (int int_x, int int_y)
{
  AIGUniqueTable *table = NULL;
  AIGVector *x = NULL;
  AIGVector *y = NULL;
  AIGVector *quotient = NULL;
  assert (!ext_allow_overflow);
  init_error_management (stderr);
  init_memory_management ();
  table = create_aig_unique_table (8);
  x = create_aig_vector ();
  y = create_aig_vector ();
  long_long_2_aig_vector (int_x, x);
  long_long_2_aig_vector (int_y, y);
  quotient = divide_aig_vector (&table, x, y);
  if (int_y == 0)
    {
      assert (quotient->undefined == AIG_TRUE);
    }
  else if ((int_x == INT_MIN) && (int_y == -1))
    {
      assert (aig_vector_2_long_long (quotient) == INT_MIN);
      assert (quotient->undefined == AIG_TRUE);
    }
  else
    {
      assert (aig_vector_2_long_long (quotient) == int_x / int_y);
      assert (quotient->undefined == AIG_FALSE);
    }
  delete_aig_vector (quotient);
  delete_aig_vector (y);
  delete_aig_vector (x);
  delete_aig_unique_table (table, b_false);
  finalise_memory_management ();
}

void
test_divide_aig_vector_1 ()
{
  test_divide_aig_vector (14, 3);
}

void
test_divide_aig_vector_2 ()
{
  test_divide_aig_vector (14, -3);
}

void
test_divide_aig_vector_3 ()
{
  test_divide_aig_vector (-14, 3);
}

void
test_divide_aig_vector_4 ()
{
  test_divide_aig_vector (-14, -3);
}

void
test_divide_aig_vector_5 ()
{
  test_divide_aig_vector (14, 1);
}

void
test_divide_aig_vector_6 ()
{
  test_divide_aig_vector (14, -1);
}

void
test_divide_aig_vector_7 ()
{
  test_divide_aig_vector (-14, 1);
}

void
test_divide_aig_vector_8 ()
{
  test_divide_aig_vector (-14, -1);
}

void
test_divide_aig_vector_9 ()
{
  test_divide_aig_vector (INT_MIN, INT_MIN);
}

void
test_divide_aig_vector_10 ()
{
  test_divide_aig_vector (INT_MIN, INT_MAX);
}

void
test_divide_aig_vector_11 ()
{
  test_divide_aig_vector (INT_MAX, INT_MIN);
}

void
test_divide_aig_vector_12 ()
{
  test_divide_aig_vector (INT_MAX, INT_MAX);
}

void
test_divide_aig_vector_13 ()
{
  test_divide_aig_vector (INT_MIN, 1);
}

void
test_divide_aig_vector_14 ()
{
  test_divide_aig_vector (1, INT_MIN);
}

void
test_divide_aig_vector_15 ()
{
  test_divide_aig_vector (INT_MIN, -1);
}

void
test_divide_aig_vector_16 ()
{
  test_divide_aig_vector (-1, INT_MIN);
}

void
test_divide_aig_vector_17 ()
{
  test_divide_aig_vector (INT_MAX, 1);
}

void
test_divide_aig_vector_18 ()
{
  test_divide_aig_vector (1, INT_MAX);
}

void
test_divide_aig_vector_19 ()
{
  test_divide_aig_vector (INT_MAX, -1);
}

void
test_divide_aig_vector_20 ()
{
  test_divide_aig_vector (-1, INT_MAX);
}

void
test_divide_aig_vector_21 ()
{
  test_divide_aig_vector (0, INT_MAX);
}

void
test_divide_aig_vector_22 ()
{
  test_divide_aig_vector (0, INT_MIN);
}

void
test_divide_aig_vector_23 ()
{
  test_divide_aig_vector (0, 1);
}

void
test_divide_aig_vector_24 ()
{
  test_divide_aig_vector (0, -1);
}

void
test_divide_aig_vector_25 ()
{
  test_divide_aig_vector (INT_MAX, 0);
}

void
test_divide_aig_vector_26 ()
{
  test_divide_aig_vector (INT_MIN, 0);
}

void
test_divide_aig_vector_27 ()
{
  test_divide_aig_vector (0, 0);
}

void
test_divide_aig_vector_undefined ()
{
  AIGVector *x = NULL;
  AIGVector *y = NULL;
  AIGVector *result = NULL;
  AIGUniqueTable *table = NULL;
  assert (!ext_allow_overflow);
  init_error_management (stderr);
  init_memory_management ();
  table = create_aig_unique_table (8);
  x = create_aig_vector ();
  y = create_aig_vector ();

  long_long_2_aig_vector (0, x);
  long_long_2_aig_vector (0, y);
  result = divide_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = divide_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_TRUE;
  result = divide_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = divide_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_FALSE;

  long_long_2_aig_vector (1, x);
  long_long_2_aig_vector (0, y);
  result = divide_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = divide_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_TRUE;
  result = divide_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = divide_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_FALSE;

  long_long_2_aig_vector (0, x);
  long_long_2_aig_vector (1, y);
  result = divide_aig_vector (&table, x, y);
  assert (result->undefined == AIG_FALSE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = divide_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_TRUE;
  result = divide_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = divide_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_FALSE;

  long_long_2_aig_vector (1, x);
  long_long_2_aig_vector (1, y);
  result = divide_aig_vector (&table, x, y);
  assert (result->undefined == AIG_FALSE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = divide_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_TRUE;
  result = divide_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = divide_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_FALSE;

  long_long_2_aig_vector (INT_MIN, x);
  long_long_2_aig_vector (-1, y);
  result = divide_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = divide_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_TRUE;
  result = divide_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = divide_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_FALSE;

  ext_allow_overflow = b_true;

  long_long_2_aig_vector (INT_MIN, x);
  long_long_2_aig_vector (-1, y);
  result = divide_aig_vector (&table, x, y);
  assert (result->undefined == AIG_FALSE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = divide_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_TRUE;
  result = divide_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = divide_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  delete_aig_vector (x);
  delete_aig_vector (y);
  delete_aig_unique_table (table, b_false);
  finalise_memory_management ();
  ext_allow_overflow = b_false;
}

void
test_divide_aig_vector_random ()
{
  run_void_int_int_function_random (test_divide_aig_vector,
                                    AIG_VECTOR_TEST_NUM_RANDOM_TESTS);
}

void
test_divide_aig_vector_releases ()
{
  AIGVector *x = NULL;
  AIGVector *y = NULL;
  AIGVector *quotient = NULL;
  AIGUniqueTable *table = NULL;
  int i = 0;
  init_error_management (stderr);
  init_memory_management ();
  assert (!ext_allow_overflow);
  x = create_aig_vector ();
  y = create_aig_vector ();
  table = create_aig_unique_table (8);
  for (i = 0; i < 32; i++)
    {
      x->aig[i] = var_aig (&table, i + 1);
      y->aig[i] = var_aig (&table, i + 32 + 1);
    }
  quotient = divide_aig_vector (&table, x, y);
  release_aig_vector (&table, quotient);
  release_aig_vector (&table, x);
  release_aig_vector (&table, y);
  delete_aig_vector (quotient);
  delete_aig_vector (x);
  delete_aig_vector (y);
  delete_aig_unique_table (table, b_false);
  ext_allow_overflow = b_true;
  x = create_aig_vector ();
  y = create_aig_vector ();
  table = create_aig_unique_table (8);
  for (i = 0; i < 32; i++)
    {
      x->aig[i] = var_aig (&table, i + 1);
      y->aig[i] = var_aig (&table, i + 32 + 1);
    }
  quotient = divide_aig_vector (&table, x, y);
  release_aig_vector (&table, quotient);
  release_aig_vector (&table, x);
  release_aig_vector (&table, y);
  delete_aig_vector (quotient);
  delete_aig_vector (x);
  delete_aig_vector (y);
  delete_aig_unique_table (table, b_false);
  finalise_memory_management ();
  ext_allow_overflow = b_false;
}

void
test_modulo_aig_vector (int int_x, int int_y)
{
  AIGUniqueTable *table = NULL;
  AIGVector *x = NULL;
  AIGVector *y = NULL;
  AIGVector *remainder = NULL;
  init_error_management (stderr);
  init_memory_management ();
  table = create_aig_unique_table (8);
  x = create_aig_vector ();
  y = create_aig_vector ();
  long_long_2_aig_vector (int_x, x);
  long_long_2_aig_vector (int_y, y);
  remainder = modulo_aig_vector (&table, x, y);
  if (int_y == 0)
    {
      assert (remainder->undefined == AIG_TRUE);
    }
  else
    {
      if ((int_x == INT_MIN) && (int_y == -1))
        {
          assert (aig_vector_2_long_long (remainder) == 0);
        }
      else
        {
          assert (aig_vector_2_long_long (remainder) == int_x % int_y);
        }
      assert (remainder->undefined == AIG_FALSE);
    }
  delete_aig_vector (remainder);
  delete_aig_vector (y);
  delete_aig_vector (x);
  delete_aig_unique_table (table, b_false);
  finalise_memory_management ();
}

void
test_modulo_aig_vector_1 ()
{
  test_modulo_aig_vector (14, 3);
}

void
test_modulo_aig_vector_2 ()
{
  test_modulo_aig_vector (14, -3);
}

void
test_modulo_aig_vector_3 ()
{
  test_modulo_aig_vector (-14, 3);
}

void
test_modulo_aig_vector_4 ()
{
  test_modulo_aig_vector (-14, -3);
}

void
test_modulo_aig_vector_5 ()
{
  test_modulo_aig_vector (14, 1);
}

void
test_modulo_aig_vector_6 ()
{
  test_modulo_aig_vector (14, -1);
}

void
test_modulo_aig_vector_7 ()
{
  test_modulo_aig_vector (-14, 1);
}

void
test_modulo_aig_vector_8 ()
{
  test_modulo_aig_vector (-14, -1);
}

void
test_modulo_aig_vector_9 ()
{
  test_modulo_aig_vector (INT_MIN, INT_MIN);
}

void
test_modulo_aig_vector_10 ()
{
  test_modulo_aig_vector (INT_MIN, INT_MAX);
}

void
test_modulo_aig_vector_11 ()
{
  test_modulo_aig_vector (INT_MAX, INT_MIN);
}

void
test_modulo_aig_vector_12 ()
{
  test_modulo_aig_vector (INT_MAX, INT_MAX);
}

void
test_modulo_aig_vector_13 ()
{
  test_modulo_aig_vector (INT_MIN, 1);
}

void
test_modulo_aig_vector_14 ()
{
  test_modulo_aig_vector (1, INT_MIN);
}

void
test_modulo_aig_vector_15 ()
{
  test_modulo_aig_vector (INT_MIN, -1);
}

void
test_modulo_aig_vector_16 ()
{
  test_modulo_aig_vector (-1, INT_MIN);
}

void
test_modulo_aig_vector_17 ()
{
  test_modulo_aig_vector (INT_MAX, 1);
}

void
test_modulo_aig_vector_18 ()
{
  test_modulo_aig_vector (1, INT_MAX);
}

void
test_modulo_aig_vector_19 ()
{
  test_modulo_aig_vector (INT_MAX, -1);
}

void
test_modulo_aig_vector_20 ()
{
  test_modulo_aig_vector (-1, INT_MAX);
}

void
test_modulo_aig_vector_21 ()
{
  test_modulo_aig_vector (0, INT_MAX);
}

void
test_modulo_aig_vector_22 ()
{
  test_modulo_aig_vector (0, INT_MIN);
}

void
test_modulo_aig_vector_23 ()
{
  test_modulo_aig_vector (0, 1);
}

void
test_modulo_aig_vector_24 ()
{
  test_modulo_aig_vector (0, -1);
}

void
test_modulo_aig_vector_25 ()
{
  test_modulo_aig_vector (INT_MAX, 0);
}

void
test_modulo_aig_vector_26 ()
{
  test_modulo_aig_vector (INT_MIN, 0);
}

void
test_modulo_aig_vector_27 ()
{
  test_modulo_aig_vector (0, 0);
}

void
test_modulo_aig_vector_undefined ()
{
  AIGVector *x = NULL;
  AIGVector *y = NULL;
  AIGVector *result = NULL;
  AIGUniqueTable *table = NULL;
  init_error_management (stderr);
  init_memory_management ();
  table = create_aig_unique_table (8);
  x = create_aig_vector ();
  y = create_aig_vector ();

  long_long_2_aig_vector (0, x);
  long_long_2_aig_vector (0, y);
  result = modulo_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = modulo_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_TRUE;
  result = modulo_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = modulo_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_FALSE;

  long_long_2_aig_vector (1, x);
  long_long_2_aig_vector (0, y);
  result = modulo_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = modulo_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_TRUE;
  result = modulo_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = modulo_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_FALSE;

  long_long_2_aig_vector (0, x);
  long_long_2_aig_vector (1, y);
  result = modulo_aig_vector (&table, x, y);
  assert (result->undefined == AIG_FALSE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = modulo_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_TRUE;
  result = modulo_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = modulo_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_FALSE;

  long_long_2_aig_vector (1, x);
  long_long_2_aig_vector (1, y);
  result = modulo_aig_vector (&table, x, y);
  assert (result->undefined == AIG_FALSE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = modulo_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_FALSE;
  y->undefined = AIG_TRUE;
  result = modulo_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  x->undefined = AIG_TRUE;
  result = modulo_aig_vector (&table, x, y);
  assert (result->undefined == AIG_TRUE);
  delete_aig_vector (result);
  delete_aig_vector (x);
  delete_aig_vector (y);
  delete_aig_unique_table (table, b_false);
  finalise_memory_management ();
}

void
test_modulo_aig_vector_random ()
{
  run_void_int_int_function_random (test_modulo_aig_vector,
                                    AIG_VECTOR_TEST_NUM_RANDOM_TESTS);
}

void
test_modulo_aig_vector_releases ()
{
  AIGVector *x = NULL;
  AIGVector *y = NULL;
  AIGVector *quotient = NULL;
  AIGUniqueTable *table = NULL;
  int i = 0;
  init_error_management (stderr);
  init_memory_management ();
  x = create_aig_vector ();
  y = create_aig_vector ();
  table = create_aig_unique_table (8);
  for (i = 0; i < 32; i++)
    {
      x->aig[i] = var_aig (&table, i + 1);
      y->aig[i] = var_aig (&table, i + 32 + 1);
    }
  quotient = modulo_aig_vector (&table, x, y);
  release_aig_vector (&table, quotient);
  release_aig_vector (&table, x);
  release_aig_vector (&table, y);
  delete_aig_vector (quotient);
  delete_aig_vector (x);
  delete_aig_vector (y);
  delete_aig_unique_table (table, b_false);
  finalise_memory_management ();
}

void
run_aig_vector_tests ()
{
  run_test (test_create_delete_aig_vector);
  run_test (test_release_aig_vector);
  run_test (test_copy_aig_vector);
  run_test (test_aig_vector_2_long_long_1);
  run_test (test_aig_vector_2_long_long_2);
  run_test (test_aig_vector_2_long_long_3);
  run_test (test_aig_vector_2_long_long_4);
  run_test (test_aig_vector_2_long_long_5);
  run_test (test_aig_vector_2_long_long_random);
  run_test (test_long_long_2_aig_vector_1);
  run_test (test_long_long_2_aig_vector_2);
  run_test (test_long_long_2_aig_vector_3);
  run_test (test_long_long_2_aig_vector_4);
  run_test (test_long_long_2_aig_vector_5);
  run_test (test_long_long_2_aig_vector_random);
  run_test (test_conjunction_aig_vector_1);
  run_test (test_conjunction_aig_vector_2);
  run_test (test_conjunction_aig_vector_3);
  run_test (test_conjunction_aig_vector_4);
  run_test (test_conjunction_aig_vector_5);
  run_test (test_conjunction_aig_vector_random);
  run_test (test_conjunction_aig_vector_releases);
  run_test (test_disjunction_aig_vector_1);
  run_test (test_disjunction_aig_vector_2);
  run_test (test_disjunction_aig_vector_3);
  run_test (test_disjunction_aig_vector_4);
  run_test (test_disjunction_aig_vector_5);
  run_test (test_disjunction_aig_vector_random);
  run_test (test_disjunction_aig_vector_releases);
  run_test (test_not_aig_vector_1);
  run_test (test_not_aig_vector_2);
  run_test (test_not_aig_vector_3);
  run_test (test_not_aig_vector_4);
  run_test (test_not_aig_vector_5);
  run_test (test_not_aig_vector_undefined);
  run_test (test_not_aig_vector_random);
  run_test (test_not_aig_vector_releases);
  run_test (test_and_aig_vector_1);
  run_test (test_and_aig_vector_2);
  run_test (test_and_aig_vector_3);
  run_test (test_and_aig_vector_4);
  run_test (test_and_aig_vector_5);
  run_test (test_and_aig_vector_undefined);
  run_test (test_and_aig_vector_random);
  run_test (test_and_aig_vector_releases);
  run_test (test_or_aig_vector_1);
  run_test (test_or_aig_vector_2);
  run_test (test_or_aig_vector_3);
  run_test (test_or_aig_vector_4);
  run_test (test_or_aig_vector_5);
  run_test (test_or_aig_vector_undefined);
  run_test (test_or_aig_vector_random);
  run_test (test_or_aig_vector_releases);
  run_test (test_imp_aig_vector_1);
  run_test (test_imp_aig_vector_2);
  run_test (test_imp_aig_vector_3);
  run_test (test_imp_aig_vector_4);
  run_test (test_imp_aig_vector_5);
  run_test (test_imp_aig_vector_undefined);
  run_test (test_imp_aig_vector_random);
  run_test (test_imp_aig_vector_releases);
  run_test (test_dimp_aig_vector_1);
  run_test (test_dimp_aig_vector_2);
  run_test (test_dimp_aig_vector_3);
  run_test (test_dimp_aig_vector_4);
  run_test (test_dimp_aig_vector_5);
  run_test (test_dimp_aig_vector_undefined);
  run_test (test_dimp_aig_vector_random);
  run_test (test_dimp_aig_vector_releases);
  run_test (test_invert_aig_vector_1);
  run_test (test_invert_aig_vector_2);
  run_test (test_invert_aig_vector_3);
  run_test (test_invert_aig_vector_4);
  run_test (test_invert_aig_vector_5);
  run_test (test_invert_aig_vector_undefined);
  run_test (test_invert_aig_vector_random);
  run_test (test_invert_aig_vector_releases);
  run_test (test_band_aig_vector_1);
  run_test (test_band_aig_vector_2);
  run_test (test_band_aig_vector_3);
  run_test (test_band_aig_vector_4);
  run_test (test_band_aig_vector_5);
  run_test (test_band_aig_vector_undefined);
  run_test (test_band_aig_vector_random);
  run_test (test_band_aig_vector_releases);
  run_test (test_bor_aig_vector_1);
  run_test (test_bor_aig_vector_2);
  run_test (test_bor_aig_vector_3);
  run_test (test_bor_aig_vector_4);
  run_test (test_bor_aig_vector_5);
  run_test (test_bor_aig_vector_undefined);
  run_test (test_bor_aig_vector_random);
  run_test (test_bor_aig_vector_releases);
  run_test (test_bxor_aig_vector_1);
  run_test (test_bxor_aig_vector_2);
  run_test (test_bxor_aig_vector_3);
  run_test (test_bxor_aig_vector_4);
  run_test (test_bxor_aig_vector_5);
  run_test (test_bxor_aig_vector_undefined);
  run_test (test_bxor_aig_vector_random);
  run_test (test_bxor_aig_vector_releases);
  run_test (test_add_aig_vector_1);
  run_test (test_add_aig_vector_2);
  run_test (test_add_aig_vector_3);
  run_test (test_add_aig_vector_4);
  run_test (test_add_aig_vector_5);
  run_test (test_add_aig_vector_undefined);
  run_test (test_add_aig_vector_random);
  run_test (test_add_aig_vector_releases);
  run_test (test_unary_minus_aig_vector_1);
  run_test (test_unary_minus_aig_vector_2);
  run_test (test_unary_minus_aig_vector_3);
  run_test (test_unary_minus_aig_vector_4);
  run_test (test_unary_minus_aig_vector_5);
  run_test (test_unary_minus_aig_vector_undefined);
  run_test (test_unary_minus_aig_vector_random);
  run_test (test_unary_minus_aig_vector_releases);
  run_test (test_subtract_aig_vector_1);
  run_test (test_subtract_aig_vector_2);
  run_test (test_subtract_aig_vector_3);
  run_test (test_subtract_aig_vector_4);
  run_test (test_subtract_aig_vector_5);
  run_test (test_subtract_aig_vector_undefined);
  run_test (test_subtract_aig_vector_random);
  run_test (test_subtract_aig_vector_releases);
  run_test (test_eq_aig_vector_1);
  run_test (test_eq_aig_vector_2);
  run_test (test_eq_aig_vector_3);
  run_test (test_eq_aig_vector_4);
  run_test (test_eq_aig_vector_5);
  run_test (test_eq_aig_vector_undefined);
  run_test (test_eq_aig_vector_random);
  run_test (test_eq_aig_vector_releases);
  run_test (test_neq_aig_vector_1);
  run_test (test_neq_aig_vector_2);
  run_test (test_neq_aig_vector_3);
  run_test (test_neq_aig_vector_4);
  run_test (test_neq_aig_vector_5);
  run_test (test_neq_aig_vector_undefined);
  run_test (test_neq_aig_vector_random);
  run_test (test_neq_aig_vector_releases);
  run_test (test_less_than_aig_vector_1);
  run_test (test_less_than_aig_vector_2);
  run_test (test_less_than_aig_vector_3);
  run_test (test_less_than_aig_vector_4);
  run_test (test_less_than_aig_vector_5);
  run_test (test_less_than_aig_vector_undefined);
  run_test (test_less_than_aig_vector_random);
  run_test (test_less_than_aig_vector_releases);
  run_test (test_less_than_or_equal_aig_vector_1);
  run_test (test_less_than_or_equal_aig_vector_2);
  run_test (test_less_than_or_equal_aig_vector_3);
  run_test (test_less_than_or_equal_aig_vector_4);
  run_test (test_less_than_or_equal_aig_vector_5);
  run_test (test_less_than_or_equal_aig_vector_undefined);
  run_test (test_less_than_or_equal_aig_vector_random);
  run_test (test_less_than_or_equal_aig_vector_releases);
  run_test (test_greater_than_aig_vector_1);
  run_test (test_greater_than_aig_vector_2);
  run_test (test_greater_than_aig_vector_3);
  run_test (test_greater_than_aig_vector_4);
  run_test (test_greater_than_aig_vector_5);
  run_test (test_greater_than_aig_vector_undefined);
  run_test (test_greater_than_aig_vector_random);
  run_test (test_greater_than_aig_vector_releases);
  run_test (test_greater_than_or_equal_aig_vector_1);
  run_test (test_greater_than_or_equal_aig_vector_2);
  run_test (test_greater_than_or_equal_aig_vector_3);
  run_test (test_greater_than_or_equal_aig_vector_4);
  run_test (test_greater_than_or_equal_aig_vector_5);
  run_test (test_greater_than_or_equal_aig_vector_undefined);
  run_test (test_greater_than_or_equal_aig_vector_random);
  run_test (test_greater_than_or_equal_aig_vector_releases);
  run_test (test_shift_left_aig_vector_1);
  run_test (test_shift_left_aig_vector_2);
  run_test (test_shift_left_aig_vector_3);
  run_test (test_shift_left_aig_vector_4);
  run_test (test_shift_left_aig_vector_5);
  run_test (test_shift_left_aig_vector_undefined);
  run_test (test_shift_left_aig_vector_random);
  run_test (test_shift_left_aig_vector_releases);
  run_test (test_shift_right_aig_vector_1);
  run_test (test_shift_right_aig_vector_2);
  run_test (test_shift_right_aig_vector_3);
  run_test (test_shift_right_aig_vector_4);
  run_test (test_shift_right_aig_vector_5);
  run_test (test_shift_right_aig_vector_undefined);
  run_test (test_shift_right_aig_vector_random);
  run_test (test_shift_right_aig_vector_releases);
  run_test (test_multiply_aig_vector_1);
  run_test (test_multiply_aig_vector_2);
  run_test (test_multiply_aig_vector_3);
  run_test (test_multiply_aig_vector_4);
  run_test (test_multiply_aig_vector_5);
  run_test (test_multiply_aig_vector_6);
  run_test (test_multiply_aig_vector_7);
  run_test (test_multiply_aig_vector_8);
  run_test (test_multiply_aig_vector_9);
  run_test (test_multiply_aig_vector_10);
  run_test (test_multiply_aig_vector_11);
  run_test (test_multiply_aig_vector_12);
  run_test (test_multiply_aig_vector_13);
  run_test (test_multiply_aig_vector_14);
  run_test (test_multiply_aig_vector_15);
  run_test (test_multiply_aig_vector_16);
  run_test (test_multiply_aig_vector_17);
  run_test (test_multiply_aig_vector_18);
  run_test (test_multiply_aig_vector_19);
  run_test (test_multiply_aig_vector_20);
  run_test (test_multiply_aig_vector_21);
  run_test (test_multiply_aig_vector_22);
  run_test (test_multiply_aig_vector_undefined);
  run_test (test_multiply_aig_vector_random);
  run_test (test_multiply_aig_vector_releases);
  run_test (test_if_then_else_aig_vector_1);
  run_test (test_if_then_else_aig_vector_2);
  run_test (test_if_then_else_aig_vector_3);
  run_test (test_if_then_else_aig_vector_4);
  run_test (test_if_then_else_aig_vector_5);
  run_test (test_if_then_else_aig_vector_6);
  run_test (test_if_then_else_aig_vector_7);
  run_test (test_if_then_else_aig_vector_8);
  run_test (test_if_then_else_aig_vector_undefined);
  run_test (test_if_then_else_aig_vector_random);
  run_test (test_if_then_else_aig_vector_releases);
  run_test (test_divide_aig_vector_1);
  run_test (test_divide_aig_vector_2);
  run_test (test_divide_aig_vector_3);
  run_test (test_divide_aig_vector_4);
  run_test (test_divide_aig_vector_5);
  run_test (test_divide_aig_vector_6);
  run_test (test_divide_aig_vector_7);
  run_test (test_divide_aig_vector_8);
  run_test (test_divide_aig_vector_9);
  run_test (test_divide_aig_vector_10);
  run_test (test_divide_aig_vector_11);
  run_test (test_divide_aig_vector_12);
  run_test (test_divide_aig_vector_13);
  run_test (test_divide_aig_vector_14);
  run_test (test_divide_aig_vector_15);
  run_test (test_divide_aig_vector_16);
  run_test (test_divide_aig_vector_17);
  run_test (test_divide_aig_vector_18);
  run_test (test_divide_aig_vector_19);
  run_test (test_divide_aig_vector_20);
  run_test (test_divide_aig_vector_21);
  run_test (test_divide_aig_vector_22);
  run_test (test_divide_aig_vector_23);
  run_test (test_divide_aig_vector_24);
  run_test (test_divide_aig_vector_25);
  run_test (test_divide_aig_vector_26);
  run_test (test_divide_aig_vector_27);
  run_test (test_divide_aig_vector_undefined);
  run_test (test_divide_aig_vector_random);
  run_test (test_divide_aig_vector_releases);
  run_test (test_modulo_aig_vector_1);
  run_test (test_modulo_aig_vector_2);
  run_test (test_modulo_aig_vector_3);
  run_test (test_modulo_aig_vector_4);
  run_test (test_modulo_aig_vector_5);
  run_test (test_modulo_aig_vector_6);
  run_test (test_modulo_aig_vector_7);
  run_test (test_modulo_aig_vector_8);
  run_test (test_modulo_aig_vector_9);
  run_test (test_modulo_aig_vector_10);
  run_test (test_modulo_aig_vector_11);
  run_test (test_modulo_aig_vector_12);
  run_test (test_modulo_aig_vector_13);
  run_test (test_modulo_aig_vector_14);
  run_test (test_modulo_aig_vector_15);
  run_test (test_modulo_aig_vector_16);
  run_test (test_modulo_aig_vector_17);
  run_test (test_modulo_aig_vector_18);
  run_test (test_modulo_aig_vector_19);
  run_test (test_modulo_aig_vector_20);
  run_test (test_modulo_aig_vector_21);
  run_test (test_modulo_aig_vector_22);
  run_test (test_modulo_aig_vector_23);
  run_test (test_modulo_aig_vector_24);
  run_test (test_modulo_aig_vector_25);
  run_test (test_modulo_aig_vector_26);
  run_test (test_modulo_aig_vector_27);
  run_test (test_modulo_aig_vector_undefined);
  run_test (test_modulo_aig_vector_random);
  run_test (test_modulo_aig_vector_releases);
}
