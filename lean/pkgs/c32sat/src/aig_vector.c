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
#include "aig.h"
#include "aig_vector.h"
#include "c32sat_math.h"
#include "memory_management.h"
#include "config.h"

AIGVector *
create_aig_vector ()
{
  int i = 0;
  AIGVector *result = (AIGVector *) malloc_c32sat (sizeof (AIGVector));
  result->aig = (AIG **) malloc_c32sat (sizeof (AIG *) * ext_number_of_bits);
  for (i = 0; i < ext_number_of_bits; i++)
    {
      result->aig[i] = AIG_FALSE;
    }
  result->undefined = AIG_FALSE;
  return result;
}

void
delete_aig_vector (AIGVector * aig_vector)
{
  assert (aig_vector != NULL);
  free_c32sat (aig_vector->aig, sizeof (AIG *) * ext_number_of_bits);
  free_c32sat (aig_vector, sizeof (AIGVector));
}

AIGVector *
copy_aig_vector (AIGUniqueTable ** table, AIGVector * aig_vector)
{
  int i = 0;
  AIGVector *result = NULL;
  assert (table != NULL && *table != NULL && aig_vector != NULL);
  result = create_aig_vector ();
  for (i = 0; i < ext_number_of_bits; i++)
    {
      result->aig[i] = copy_aig (table, aig_vector->aig[i]);
    }
  result->undefined = copy_aig (table, aig_vector->undefined);
  return result;
}

void
release_aig_vector (AIGUniqueTable ** table, AIGVector * aig_vector)
{
  int i = 0;
  assert (table != NULL && *table != NULL && aig_vector != NULL);
  for (i = 0; i < ext_number_of_bits; i++)
    {
      release_aig (table, aig_vector->aig[i]);
    }
  release_aig (table, aig_vector->undefined);
}

long long int
aig_vector_2_long_long (AIGVector * aig_vector)
{
  int bin[ext_number_of_bits];
  int i = 0;
  assert (aig_vector != NULL);
  for (i = 0; i < ext_number_of_bits; i++)
    {
      assert (is_aig_constant (aig_vector->aig[i]));
      bin[i] = aig_vector->aig[i] == AIG_TRUE ? 1 : 0;
    }
  return bin_2_long_long_c32sat_math (bin, ext_number_of_bits);
}

void
long_long_2_aig_vector (long long int x, AIGVector * result)
{
  int bin[ext_number_of_bits];
  int i = 0;
  assert (result != NULL);
  long_long_2_bin_c32sat_math (x, bin, ext_number_of_bits);
  for (i = 0; i < ext_number_of_bits; i++)
    {
      result->aig[i] = bin[i] ? AIG_TRUE : AIG_FALSE;
    }
}

AIG *
conjunction_aig_vector (AIGUniqueTable ** table, AIGVector * aig_vector)
{
  AIG *temp[ext_number_of_bits];
  int i = 0;
  assert (table != NULL && aig_vector != NULL);
  for (i = 0; i < ext_number_of_bits; i++)
    {
      temp[i] = aig_vector->aig[i];
    }
  return and_aig_array (table, temp, ext_number_of_bits);
}

AIG *
disjunction_aig_vector (AIGUniqueTable ** table, AIGVector * aig_vector)
{
  AIG *temp[ext_number_of_bits];
  int i = 0;
  assert (table != NULL && aig_vector != NULL);
  for (i = 0; i < ext_number_of_bits; i++)
    {
      temp[i] = aig_vector->aig[i];
    }
  return or_aig_array (table, temp, ext_number_of_bits);
}

AIGVector *
not_aig_vector (AIGUniqueTable ** table, AIGVector * x)
{
  AIGVector *result = NULL;
  assert (table != NULL && *table != NULL && x != NULL);
  result = create_aig_vector ();
  result->aig[0] = invert_aig (disjunction_aig_vector (table, x));
  result->undefined = copy_aig (table, x->undefined);
  return result;
}

AIGVector *
and_aig_vector (AIGUniqueTable ** table, AIGVector * x, AIGVector * y)
{
  AIGVector *result = NULL;
  AIG *temp1 = NULL;
  AIG *temp2 = NULL;
  AIG *temp3 = NULL;
  assert (table != NULL && *table != NULL && x != NULL && y != NULL);
  result = create_aig_vector ();
  temp1 = disjunction_aig_vector (table, x);
  temp2 = disjunction_aig_vector (table, y);
  result->aig[0] = and_aig (table, temp1, temp2);
  temp3 = and_aig (table, temp1, y->undefined);
  result->undefined = or_aig(table, x->undefined, temp3);
  release_aig (table, temp1);
  release_aig (table, temp2);
  release_aig (table, temp3);
  return result;
}

AIGVector *
or_aig_vector (AIGUniqueTable ** table, AIGVector * x, AIGVector * y)
{
  AIGVector *result = NULL;
  AIG *temp1 = NULL;
  AIG *temp2 = NULL;
  AIG *temp3 = NULL;
  assert (table != NULL && *table != NULL && x != NULL && y != NULL);
  result = create_aig_vector ();
  temp1 = disjunction_aig_vector (table, x);
  temp2 = disjunction_aig_vector (table, y);
  result->aig[0] = or_aig (table, temp1, temp2);
  temp3 = and_aig (table, invert_aig (temp1), y->undefined);
  result->undefined = or_aig (table, x->undefined, temp3);
  release_aig (table, temp1);
  release_aig (table, temp2);
  release_aig (table, temp3);
  return result;
}

AIGVector *
imp_aig_vector (AIGUniqueTable ** table, AIGVector * x, AIGVector * y)
{
  AIGVector *result = NULL;
  AIGVector *not_x = NULL;
  assert (table != NULL && *table != NULL && x != NULL && y != NULL);
  not_x = not_aig_vector (table, x);
  result = or_aig_vector (table, not_x, y);
  release_aig_vector (table, not_x);
  delete_aig_vector (not_x);
  return result;
}

AIGVector *
dimp_aig_vector (AIGUniqueTable ** table, AIGVector * x, AIGVector * y)
{
  AIGVector *result = NULL;
  AIG *temp1 = NULL;
  AIG *temp2 = NULL;
  AIG *temp3 = NULL;
  AIG *temp4 = NULL;
  assert (table != NULL && *table != NULL && x != NULL && y != NULL);
  result = create_aig_vector ();
  temp1 = disjunction_aig_vector (table, x);
  temp2 = disjunction_aig_vector (table, y);
  temp3 = or_aig (table, invert_aig (temp1), temp2);
  temp4 = or_aig (table, temp1, invert_aig (temp2));
  result->aig[0] = and_aig (table, temp3, temp4);
  release_aig (table, temp1);
  release_aig (table, temp2);
  release_aig (table, temp3);
  release_aig (table, temp4);
  result->undefined = or_aig (table, x->undefined, y->undefined);
  return result;
}

void
invert_aig_vector (AIGVector * aig_vector)
{
  int i = 0;
  assert (aig_vector != NULL);
  for (i = 0; i < ext_number_of_bits; i++)
    {
      aig_vector->aig[i] = invert_aig (aig_vector->aig[i]);
    }
}

AIGVector *
band_aig_vector (AIGUniqueTable ** table, AIGVector * x, AIGVector * y)
{
  int i = 0;
  AIGVector *result = NULL;
  assert (table != NULL && *table != NULL && x != NULL && y != NULL);
  result = create_aig_vector ();
  for (i = 0; i < ext_number_of_bits; i++)
    {
      result->aig[i] = and_aig (table, x->aig[i], y->aig[i]);
    }
  result->undefined = or_aig (table, x->undefined, y->undefined);
  return result;
}

AIGVector *
bor_aig_vector (AIGUniqueTable ** table, AIGVector * x, AIGVector * y)
{
  int i = 0;
  AIGVector *result = NULL;
  assert (table != NULL && *table != NULL && x != NULL && y != NULL);
  result = create_aig_vector ();
  for (i = 0; i < ext_number_of_bits; i++)
    {
      result->aig[i] = or_aig (table, x->aig[i], y->aig[i]);
    }
  result->undefined = or_aig (table, x->undefined, y->undefined);
  return result;
}

AIGVector *
bxor_aig_vector (AIGUniqueTable ** table, AIGVector * x, AIGVector * y)
{
  int i = 0;
  AIGVector *result = NULL;
  assert (table != NULL && *table != NULL && x != NULL && y != NULL);
  result = create_aig_vector ();
  for (i = 0; i < ext_number_of_bits; i++)
    {
      result->aig[i] = xor_aig (table, x->aig[i], y->aig[i]);
    }
  result->undefined = or_aig (table, x->undefined, y->undefined);
  return result;
}

AIGVector *
add_aig_vector (AIGUniqueTable ** table, AIGVector * x, AIGVector * y)
{
  int i = 0;
  AIG *carry = AIG_FALSE;
  AIG *temp = AIG_FALSE;
  AIG *temp2 = NULL;
  AIG *overflow = NULL;
  AIGVector *result = create_aig_vector ();
  assert (table != NULL && x != NULL && y != NULL);
  for (i = 0; i < ext_number_of_bits - 1; i++)
    {
      result->aig[i] =
        full_add_aig (table, x->aig[i], y->aig[i], carry, &temp);
      release_aig (table, carry);
      carry = temp;
    }
  result->aig[ext_number_of_bits - 1] =
    xor_aig_va_list (table, 3, x->aig[ext_number_of_bits - 1],
                     y->aig[ext_number_of_bits - 1], carry);
  temp =
    dimp_aig (table, x->aig[ext_number_of_bits - 1],
              y->aig[ext_number_of_bits - 1]);
  temp2 = dimp_aig
    (table, x->aig[ext_number_of_bits - 1],
     result->aig[ext_number_of_bits - 1]);
  overflow = and_aig (table, temp, invert_aig (temp2));
  if (ext_allow_overflow)
    {
      result->undefined = or_aig (table, x->undefined, y->undefined);
    }
  else
    {
      result->undefined =
        or_aig_va_list (table, 3, x->undefined, y->undefined, overflow);
    }
  release_aig (table, carry);
  release_aig (table, temp);
  release_aig (table, temp2);
  release_aig (table, overflow);
  return result;
}

AIGVector *
unary_minus_aig_vector (AIGUniqueTable ** table, AIGVector * x)
{
  int i = 0;
  AIGVector *temp_vector = NULL;
  AIGVector *one = NULL;
  AIGVector *result = NULL;
  AIG *temp = NULL;
  assert (table != NULL && x != NULL);
  temp_vector = create_aig_vector ();
  one = create_aig_vector ();
  one->aig[0] = AIG_TRUE;
  for (i = 0; i < ext_number_of_bits; i++)
    {
      temp_vector->aig[i] = invert_aig (x->aig[i]);
    }
  result = add_aig_vector (table, temp_vector, one);
  temp = result->undefined;
  result->undefined = or_aig (table, x->undefined, temp);
  release_aig (table, temp);
  delete_aig_vector (one);
  delete_aig_vector (temp_vector);
  return result;
}

static AIGVector *
twos_complement_aig_vector (AIGUniqueTable ** table, AIGVector * x)
{
  AIGVector *result = NULL;
  assert (table != NULL && x != NULL);
  result = unary_minus_aig_vector (table, x);
  release_aig (table, result->undefined);
  result->undefined = copy_aig (table, x->undefined);
  return result;
}

AIGVector *
subtract_aig_vector (AIGUniqueTable ** table, AIGVector * x, AIGVector * y)
{
  AIGVector *result = NULL;
  AIGVector *temp_vector = NULL;
  AIGVector *zero = NULL;
  AIGVector *int_min = NULL;
  AIGVector *greater_equal_zero = NULL;
  AIGVector *is_int_min = NULL;
  AIG *temp1 = NULL;
  AIG *temp2 = NULL;
  assert (table != NULL && *table != NULL && x != NULL && y != NULL);
  zero = create_aig_vector ();
  int_min = create_aig_vector ();
  int_min->aig[ext_number_of_bits - 1] = AIG_TRUE;
  temp_vector = twos_complement_aig_vector (table, y);
  result = add_aig_vector (table, x, temp_vector);
  greater_equal_zero = greater_than_or_equal_aig_vector (table, x, zero);
  is_int_min = eq_aig_vector (table, y, int_min);
  temp1 = and_aig (table, result->undefined, invert_aig (is_int_min->aig[0]));
  temp2 = and_aig (table, greater_equal_zero->aig[0], is_int_min->aig[0]);
  release_aig (table, result->undefined);
  if (ext_allow_overflow)
    {
      result->undefined = or_aig (table, x->undefined, y->undefined);
    }
  else
    {
      result->undefined =
        or_aig_va_list (table, 4, temp1, temp2, x->undefined, y->undefined);
    }
  release_aig (table, temp1);
  release_aig (table, temp2);
  release_aig_vector (table, temp_vector);
  release_aig_vector (table, greater_equal_zero);
  release_aig_vector (table, is_int_min);
  delete_aig_vector (temp_vector);
  delete_aig_vector (greater_equal_zero);
  delete_aig_vector (is_int_min);
  delete_aig_vector (zero);
  delete_aig_vector (int_min);
  return result;
}

AIGVector *
eq_aig_vector (AIGUniqueTable ** table, AIGVector * x, AIGVector * y)
{
  int i = 0;
  AIGVector *result = NULL;
  AIGVector *temp = NULL;
  assert (table != NULL && x != NULL && y != NULL);
  result = create_aig_vector ();
  temp = create_aig_vector ();
  for (i = 0; i < ext_number_of_bits; i++)
    {
      temp->aig[i] = dimp_aig (table, x->aig[i], y->aig[i]);
    }
  result->aig[0] = conjunction_aig_vector (table, temp);
  release_aig_vector (table, temp);
  delete_aig_vector (temp);
  result->undefined = or_aig (table, x->undefined, y->undefined);
  return result;
}

AIGVector *
neq_aig_vector (AIGUniqueTable ** table, AIGVector * x, AIGVector * y)
{
  AIGVector *result = NULL;
  assert (table != NULL && x != NULL && y != NULL);
  result = eq_aig_vector (table, x, y);
  result->aig[0] = invert_aig (result->aig[0]);
  return result;
}

void
ripple_compare_aig_vector (AIGUniqueTable ** table, AIGVector * x,
                           AIGVector * y, AIG ** lt, AIG ** eq, AIG ** gt)
{
  int i = 0;
  AIG *lt_in = NULL;
  AIG *eq_in = NULL;
  AIG *gt_in = NULL;
  assert (table != NULL && *table != NULL && x != NULL && y != NULL
          && lt != NULL && eq != NULL && gt != NULL);
  lt_in =
    and_aig (table, x->aig[ext_number_of_bits - 1],
             invert_aig (y->aig[ext_number_of_bits - 1]));
  eq_in =
    dimp_aig (table, x->aig[ext_number_of_bits - 1],
              y->aig[ext_number_of_bits - 1]);
  gt_in =
    and_aig (table, invert_aig (x->aig[ext_number_of_bits - 1]),
             y->aig[ext_number_of_bits - 1]);
  for (i = ext_number_of_bits - 2; i >= 0; i--)
    {
      ripple_compare_aig (table, x->aig[i], y->aig[i], lt_in, eq_in, gt_in,
                          lt, eq, gt);
      release_aig (table, lt_in);
      release_aig (table, eq_in);
      release_aig (table, gt_in);
      lt_in = *lt;
      eq_in = *eq;
      gt_in = *gt;
    }
}

AIGVector *
less_than_aig_vector (AIGUniqueTable ** table, AIGVector * x, AIGVector * y)
{
  AIG *lt = NULL;
  AIG *eq = NULL;
  AIG *gt = NULL;
  AIGVector *result = NULL;
  assert (table != NULL && *table != NULL && x != NULL && y != NULL);
  result = create_aig_vector ();
  ripple_compare_aig_vector (table, x, y, &lt, &eq, &gt);
  result->aig[0] = lt;
  release_aig (table, eq);
  release_aig (table, gt);
  result->undefined = or_aig (table, x->undefined, y->undefined);
  return result;
}

AIGVector *
less_than_or_equal_aig_vector (AIGUniqueTable ** table, AIGVector * x,
                               AIGVector * y)
{
  AIG *lt = NULL;
  AIG *eq = NULL;
  AIG *gt = NULL;
  AIGVector *result = NULL;
  assert (table != NULL && *table != NULL && x != NULL && y != NULL);
  result = create_aig_vector ();
  ripple_compare_aig_vector (table, x, y, &lt, &eq, &gt);
  result->aig[0] = xor_aig (table, lt, eq);
  release_aig (table, lt);
  release_aig (table, eq);
  release_aig (table, gt);
  result->undefined = or_aig (table, x->undefined, y->undefined);
  return result;
}

AIGVector *
greater_than_aig_vector (AIGUniqueTable ** table, AIGVector * x,
                         AIGVector * y)
{
  AIG *lt = NULL;
  AIG *eq = NULL;
  AIG *gt = NULL;
  AIGVector *result = NULL;
  assert (table != NULL && *table != NULL && x != NULL && y != NULL);
  result = create_aig_vector ();
  ripple_compare_aig_vector (table, x, y, &lt, &eq, &gt);
  result->aig[0] = gt;
  release_aig (table, lt);
  release_aig (table, eq);
  result->undefined = or_aig (table, x->undefined, y->undefined);
  return result;
}

AIGVector *
greater_than_or_equal_aig_vector (AIGUniqueTable ** table, AIGVector * x,
                                  AIGVector * y)
{
  AIG *lt = NULL;
  AIG *eq = NULL;
  AIG *gt = NULL;
  AIGVector *result = NULL;
  assert (table != NULL && *table != NULL && x != NULL && y != NULL);
  result = create_aig_vector ();
  ripple_compare_aig_vector (table, x, y, &lt, &eq, &gt);
  result->aig[0] = xor_aig (table, gt, eq);
  release_aig (table, lt);
  release_aig (table, eq);
  release_aig (table, gt);
  result->undefined = or_aig (table, x->undefined, y->undefined);
  return result;
}

AIGVector *
shift_n_bits_left_aig_vector (AIGUniqueTable ** table, AIGVector * x,
                              int bits, AIG * shift)
{
  AIGVector *result = NULL;
  AIG *temp1 = NULL;
  AIG *temp2 = NULL;
  AIG *temp3 = NULL;
  int i = 0;
  assert (table != NULL && *table != NULL && x != NULL && bits >= 0
          && bits < ext_number_of_bits);
  if (bits == 0)
    {
      return copy_aig_vector (table, x);
    }
  result = create_aig_vector ();
  for (i = 0; i < bits; i++)
    {
      temp1 = and_aig (table, x->aig[i], invert_aig (shift));
      temp2 = and_aig (table, AIG_FALSE, shift);
      result->aig[i] = or_aig (table, temp1, temp2);
      release_aig (table, temp1);
      release_aig (table, temp2);
    }
  for (i = bits; i < ext_number_of_bits; i++)
    {
      temp1 = and_aig (table, x->aig[i], invert_aig (shift));
      temp2 = and_aig (table, x->aig[i - bits], shift);
      result->aig[i] = or_aig (table, temp1, temp2);
      release_aig (table, temp1);
      release_aig (table, temp2);
    }
  /* is the result of shifting x left by n bits defined ? */
  temp2 =
    dimp_aig (table, x->aig[ext_number_of_bits - 1],
              x->aig[ext_number_of_bits - 2]);
  for (i = 2; i <= bits; i++)
    {
      temp1 =
        dimp_aig (table, x->aig[ext_number_of_bits - 1],
                  x->aig[ext_number_of_bits - 1 - i]);
      temp3 = and_aig (table, temp2, temp1);
      release_aig (table, temp1);
      release_aig (table, temp2);
      temp2 = temp3;
    }
  temp3 = and_aig (table, invert_aig (temp2), shift);
  result->undefined = or_aig (table, x->undefined, temp3);
  release_aig (table, temp2);
  release_aig (table, temp3);
  return result;
}

AIGVector *
shift_n_bits_right_aig_vector (AIGUniqueTable ** table, AIGVector * x,
                               int bits, AIG * shift)
{
  AIGVector *result = NULL;
  AIG *temp1 = NULL;
  AIG *temp2 = NULL;
  AIG *temp3 = NULL;
  int i = 0;
  assert (table != NULL && *table != NULL && x != NULL && bits >= 0
          && bits < ext_number_of_bits);
  if (bits == 0)
    {
      return copy_aig_vector (table, x);
    }
  result = create_aig_vector ();
  for (i = 0; i < ext_number_of_bits - bits; i++)
    {
      temp1 = and_aig (table, x->aig[i], invert_aig (shift));
      temp2 = and_aig (table, x->aig[i + bits], shift);
      result->aig[i] = or_aig (table, temp1, temp2);
      release_aig (table, temp1);
      release_aig (table, temp2);
    }
  for (i = ext_number_of_bits - bits; i < ext_number_of_bits; i++)
    {
      temp1 = and_aig (table, x->aig[i], invert_aig (shift));
      temp2 = or_aig (table, x->aig[ext_number_of_bits - 1], AIG_FALSE);
      temp3 = and_aig (table, temp2, shift);
      result->aig[i] = or_aig (table, temp1, temp3);
      release_aig (table, temp1);
      release_aig (table, temp2);
      release_aig (table, temp3);
    }
  result->undefined = copy_aig (table, x->undefined);
  return result;
}

AIGVector *
shift_left_aig_vector (AIGUniqueTable ** table, AIGVector * x, AIGVector * y)
{
  AIGVector *result = NULL;
  AIGVector *temp32 = NULL;
  AIGVector *greater_equal_bit_width = NULL;
  AIGVector *bit_width = NULL;
  AIG *overflow = NULL;
  int i = 0;
  assert (table != NULL && *table != NULL && x != NULL && y != NULL);
  result = shift_n_bits_left_aig_vector (table, x, 1, y->aig[0]);
  for (i = 1; i < log2_c32sat_math (ext_number_of_bits); i++)
    {
      temp32 = result;
      result =
        shift_n_bits_left_aig_vector (table, temp32,
                                      (int) pow2_c32sat_math (i), y->aig[i]);
      release_aig_vector (table, temp32);
      delete_aig_vector (temp32);
    }
  bit_width = create_aig_vector ();
  long_long_2_aig_vector (ext_number_of_bits, bit_width);
  greater_equal_bit_width =
    greater_than_or_equal_aig_vector (table, y, bit_width);
  overflow = result->undefined;
  if (ext_allow_overflow)
    {
      result->undefined =
        or_aig_va_list (table, 4, x->undefined, y->undefined,
                        y->aig[ext_number_of_bits - 1],
                        greater_equal_bit_width->aig[0]);
    }
  else
    {
      result->undefined =
        or_aig_va_list (table, 5, x->undefined, y->undefined,
                        y->aig[ext_number_of_bits - 1], overflow,
                        greater_equal_bit_width->aig[0]);
    }
  release_aig (table, overflow);
  release_aig_vector (table, greater_equal_bit_width);
  delete_aig_vector (bit_width);
  delete_aig_vector (greater_equal_bit_width);
  return result;
}

AIGVector *
shift_right_aig_vector (AIGUniqueTable ** table, AIGVector * x, AIGVector * y)
{
  AIGVector *result = NULL;
  AIGVector *temp32 = NULL;
  AIGVector *greater_equal_bit_width = NULL;
  AIGVector *bit_width = NULL;
  int i = 0;
  assert (table != NULL && *table != NULL && x != NULL && y != NULL);
  result = shift_n_bits_right_aig_vector (table, x, 1, y->aig[0]);
  for (i = 1; i < log2_c32sat_math (ext_number_of_bits); i++)
    {
      temp32 = result;
      result =
        shift_n_bits_right_aig_vector (table, temp32,
                                       (int) pow2_c32sat_math (i), y->aig[i]);
      release_aig_vector (table, temp32);
      delete_aig_vector (temp32);
    }
  release_aig (table, result->undefined);
  /* right operand may not be >= bit width.
     left shift operand and right shift operand may
     not be negative */
  bit_width = create_aig_vector ();
  long_long_2_aig_vector (ext_number_of_bits, bit_width);
  greater_equal_bit_width =
    greater_than_or_equal_aig_vector (table, y, bit_width);
  result->undefined =
    or_aig_va_list (table, 5, x->undefined, y->undefined,
                    x->aig[ext_number_of_bits - 1],
                    y->aig[ext_number_of_bits - 1],
                    greater_equal_bit_width->aig[0]);
  release_aig_vector (table, greater_equal_bit_width);
  delete_aig_vector (bit_width);
  delete_aig_vector (greater_equal_bit_width);
  return result;
}

AIGVector *
shift_and_add_multiplication (AIGUniqueTable ** table, AIGVector * x,
                              AIGVector * y)
{
  AIGVector *result = NULL;
  AIGVector *temp32_1 = NULL;
  AIGVector *temp32_2 = NULL;
  AIGVector *temp32_3 = NULL;
  int i = 0;
  int j = 0;
  assert (table != NULL && *table != NULL && x != NULL && y != NULL);
  temp32_1 = create_aig_vector ();
  result = create_aig_vector ();
  for (i = 0; i < ext_number_of_bits; i++)
    {
      for (j = 0; j < ext_number_of_bits; j++)
        {
          temp32_1->aig[j] = and_aig (table, x->aig[j], y->aig[i]);
        }
      temp32_2 = shift_n_bits_left_aig_vector (table, temp32_1, i, AIG_TRUE);
      temp32_3 = add_aig_vector (table, result, temp32_2);
      release_aig_vector (table, result);
      delete_aig_vector (result);
      result = temp32_3;
      release_aig_vector (table, temp32_2);
      delete_aig_vector (temp32_2);
      release_aig_vector (table, temp32_1);
    }
  delete_aig_vector (temp32_1);
  release_aig (table, result->undefined);
  result->undefined = or_aig (table, x->undefined, y->undefined);
  return result;
}

AIGVector *
add_aig_vector_carry_out (AIGUniqueTable ** table, AIGVector * x,
                          AIGVector * y, AIG ** carry_out)
{
  int i = 0;
  AIG *carry = AIG_FALSE;
  AIG *temp = NULL;
  AIGVector *result = create_aig_vector ();
  assert (table != NULL && x != NULL && y != NULL && carry_out != NULL);
  for (i = 0; i < ext_number_of_bits - 1; i++)
    {
      result->aig[i] =
        full_add_aig (table, x->aig[i], y->aig[i], carry, &temp);
      release_aig (table, carry);
      carry = temp;
    }
  result->aig[ext_number_of_bits - 1] =
    xor_aig_va_list (table, 3, x->aig[ext_number_of_bits - 1],
                     y->aig[ext_number_of_bits - 1], carry);
  *carry_out = carry;
  assert (result->undefined == AIG_FALSE);
  result->undefined =
    or_aig_va_list (table, 3, carry, x->undefined, y->undefined);
  return result;
}

AIGVector *
shift_and_add_multiplication_no_overflow (AIGUniqueTable ** table,
                                          AIGVector * x, AIGVector * y)
{
  AIGVector *x_comp = NULL;
  AIGVector *y_comp = NULL;
  AIGVector *is_x_neg = NULL;
  AIGVector *is_x_zero = NULL;
  AIGVector *is_x_one = NULL;
  AIGVector *is_x_int_min = NULL;
  AIGVector *is_y_neg = NULL;
  AIGVector *is_y_zero = NULL;
  AIGVector *is_y_one = NULL;
  AIGVector *is_y_int_min = NULL;
  AIGVector *is_result_int_min = NULL;
  AIGVector *need_neg_result = NULL;
  AIGVector *normalised_x = NULL;
  AIGVector *normalised_y = NULL;
  AIGVector *normalised_result = NULL;
  AIGVector *zero = NULL;
  AIGVector *one = NULL;
  AIGVector *int_min = NULL;
  AIGVector *result = NULL;
  AIGVector *result_comp = NULL;
  AIGVector *and_result = NULL;
  AIGVector *shift_result = NULL;
  AIGVector *add_result = NULL;
  AIGVector *num_carries = NULL;
  AIGVector *no_carry_overflow_occurred = NULL;
  AIGVector *temp_carry = NULL;
  AIGVector *temp_carry_sum_result = NULL;
  AIG *is_x_zero_or_one = NULL;
  AIG *is_y_zero_or_one = NULL;
  AIG *special_overflow_case = NULL;
  AIG *overflow_occurred = NULL;
  AIG *overflow_correction = NULL;
  AIG *overflow = NULL;
  AIG *temp1 = NULL;
  AIG *temp2 = NULL;
  AIG *carry_out = NULL;
  int i = 0;
  int j = 0;
  assert (table != NULL && *table != NULL && x != NULL && y != NULL);
  and_result = create_aig_vector ();
  result = create_aig_vector ();
  num_carries = create_aig_vector ();
  x_comp = twos_complement_aig_vector (table, x);
  y_comp = twos_complement_aig_vector (table, y);
  zero = create_aig_vector ();
  one = create_aig_vector ();
  one->aig[0] = AIG_TRUE;
  int_min = create_aig_vector ();
  int_min->aig[ext_number_of_bits - 1] = AIG_TRUE;
  is_x_neg = less_than_aig_vector (table, x, zero);
  is_x_zero = eq_aig_vector (table, x, zero);
  is_x_one = eq_aig_vector (table, x, one);
  is_x_int_min = eq_aig_vector (table, x, int_min);
  is_y_neg = less_than_aig_vector (table, y, zero);
  is_y_zero = eq_aig_vector (table, y, zero);
  is_y_one = eq_aig_vector (table, y, one);
  is_y_int_min = eq_aig_vector (table, y, int_min);
  need_neg_result = create_aig_vector ();
  normalised_x = if_then_else_aig_vector (table, is_x_neg, x_comp, x);
  normalised_y = if_then_else_aig_vector (table, is_y_neg, y_comp, y);
  for (i = 0; i < ext_number_of_bits; i++)
    {
      for (j = 0; j < ext_number_of_bits; j++)
        {
          and_result->aig[j] =
            and_aig (table, normalised_x->aig[j], normalised_y->aig[i]);
        }
      shift_result =
        shift_n_bits_left_aig_vector (table, and_result, i, AIG_TRUE);
      add_result =
        add_aig_vector_carry_out (table, result, shift_result, &carry_out);
      release_aig_vector (table, result);
      delete_aig_vector (result);
      result = add_result;
      temp_carry = create_aig_vector ();
      temp_carry->aig[0] = carry_out;
      temp_carry_sum_result = add_aig_vector (table, num_carries, temp_carry);
      release_aig_vector (table, num_carries);
      delete_aig_vector (num_carries);
      num_carries = temp_carry_sum_result;
      release_aig_vector (table, shift_result);
      delete_aig_vector (shift_result);
      release_aig_vector (table, and_result);
      release_aig (table, carry_out);
      delete_aig_vector (temp_carry);
    }
  no_carry_overflow_occurred = eq_aig_vector (table, num_carries, zero);
  is_result_int_min = eq_aig_vector (table, result, int_min);
  result_comp = twos_complement_aig_vector (table, result);
  temp1 = and_aig (table, is_x_neg->aig[0], invert_aig (is_y_neg->aig[0]));
  temp2 = and_aig (table, invert_aig (is_x_neg->aig[0]), is_y_neg->aig[0]);
  need_neg_result->aig[0] = or_aig (table, temp1, temp2);
  normalised_result =
    if_then_else_aig_vector (table, need_neg_result, result_comp, result);
  release_aig (table, temp1);
  release_aig (table, temp2);
  release_aig_vector (table, x_comp);
  release_aig_vector (table, y_comp);
  release_aig_vector (table, result_comp);
  release_aig_vector (table, normalised_x);
  release_aig_vector (table, normalised_y);
  delete_aig_vector (and_result);
  delete_aig_vector (x_comp);
  delete_aig_vector (y_comp);
  delete_aig_vector (result_comp);
  delete_aig_vector (normalised_x);
  delete_aig_vector (normalised_y);
  delete_aig_vector (zero);
  delete_aig_vector (one);
  delete_aig_vector (int_min);
  /* is the result undefined ? */
  is_x_zero_or_one = or_aig (table, is_x_zero->aig[0], is_x_one->aig[0]);
  is_y_zero_or_one = or_aig (table, is_y_zero->aig[0], is_y_one->aig[0]);
  temp1 =
    and_aig (table, invert_aig (is_x_zero_or_one), is_y_int_min->aig[0]);
  temp2 =
    and_aig (table, invert_aig (is_y_zero_or_one), is_x_int_min->aig[0]);
  special_overflow_case = or_aig (table, temp1, temp2);
  release_aig (table, temp1);
  release_aig (table, temp2);
  overflow_occurred = normalised_result->undefined;
  overflow_correction =
    and_aig_va_list (table, 3, need_neg_result->aig[0],
                     is_result_int_min->aig[0],
                     no_carry_overflow_occurred->aig[0]);
  overflow =
    and_aig (table, overflow_occurred, invert_aig (overflow_correction));
  normalised_result->undefined =
    or_aig_va_list (table, 4, x->undefined, y->undefined, overflow,
                    special_overflow_case);
  release_aig (table, overflow);
  release_aig (table, overflow_correction);
  release_aig (table, special_overflow_case);
  release_aig (table, is_x_zero_or_one);
  release_aig (table, is_y_zero_or_one);
  release_aig (table, overflow_occurred);
  release_aig_vector (table, num_carries);
  release_aig_vector (table, no_carry_overflow_occurred);
  release_aig_vector (table, is_x_neg);
  release_aig_vector (table, is_x_zero);
  release_aig_vector (table, is_x_one);
  release_aig_vector (table, is_x_int_min);
  release_aig_vector (table, is_y_neg);
  release_aig_vector (table, is_y_zero);
  release_aig_vector (table, is_y_one);
  release_aig_vector (table, is_y_int_min);
  release_aig_vector (table, is_result_int_min);
  release_aig_vector (table, result);
  release_aig_vector (table, need_neg_result);
  delete_aig_vector (is_x_neg);
  delete_aig_vector (is_x_zero);
  delete_aig_vector (is_x_one);
  delete_aig_vector (is_x_int_min);
  delete_aig_vector (is_y_neg);
  delete_aig_vector (is_y_zero);
  delete_aig_vector (is_y_one);
  delete_aig_vector (is_y_int_min);
  delete_aig_vector (num_carries);
  delete_aig_vector (no_carry_overflow_occurred);
  delete_aig_vector (is_result_int_min);
  delete_aig_vector (need_neg_result);
  delete_aig_vector (result);
  return normalised_result;
}

AIGVector *
multiply_aig_vector (AIGUniqueTable ** table, AIGVector * x, AIGVector * y)
{
  assert (table != NULL && *table != NULL && x != NULL && y != NULL);
  if (ext_allow_overflow)
    {
      return shift_and_add_multiplication (table, x, y);
    }
  else
    {
      return shift_and_add_multiplication_no_overflow (table, x, y);
    }
}

AIGVector *
if_then_else_aig_vector (AIGUniqueTable ** table, AIGVector * condition,
                         AIGVector * if_case, AIGVector * else_case)
{
  int i = 0;
  AIGVector *result = NULL;
  AIG *temp1 = NULL;
  AIG *temp2 = NULL;
  AIG *condition_aig = NULL;
  assert (table != NULL && *table != NULL && condition != NULL
          && if_case != NULL && else_case != NULL);
  result = create_aig_vector ();
  condition_aig = disjunction_aig_vector (table, condition);
  for (i = 0; i < ext_number_of_bits; i++)
    {
      temp1 = and_aig (table, if_case->aig[i], condition_aig);
      temp2 = and_aig (table, else_case->aig[i], invert_aig (condition_aig));
      result->aig[i] = or_aig (table, temp1, temp2);
      release_aig (table, temp1);
      release_aig (table, temp2);
    }
  assert (result->undefined == AIG_FALSE);
  temp1 = and_aig (table, condition_aig, if_case->undefined);
  temp2 = and_aig (table, invert_aig (condition_aig), else_case->undefined);
  result->undefined = or_aig_va_list (table, 3, condition->undefined, temp1, temp2);
  release_aig (table, condition_aig);
  release_aig (table, temp1);
  release_aig (table, temp2);
  return result;
}

void
divide_and_remainder_aig_vector (AIGUniqueTable ** table, AIGVector * x,
                                 AIGVector * y, AIGVector ** quotient,
                                 AIGVector ** remainder)
{
  AIGVector *x_neg_cond = NULL;
  AIGVector *y_neg_cond = NULL;
  AIGVector *x_neg = NULL;
  AIGVector *y_neg = NULL;
  AIGVector *zero = NULL;
  AIGVector *divisor_neg = NULL;
  AIGVector *temp = NULL;
  AIGVector *quotient_temp = NULL;
  AIGVector *subtraction_result = NULL;
  AIGVector *subtraction_result_neg_cond = NULL;
  AIGVector *quotient_neg = NULL;
  AIGVector *remainder_neg = NULL;
  AIGVector *quotient_neg_cond = NULL;
  AIG *eq = NULL;
  AIG *gt = NULL;
  AIG *lt = NULL;
  int i = 0;
  assert (table != NULL && *table != NULL && x != NULL && y != NULL
          && quotient != NULL && remainder != NULL);
  zero = create_aig_vector ();
  x_neg_cond = create_aig_vector ();
  y_neg_cond = create_aig_vector ();
  /* normalisation */
  ripple_compare_aig_vector (table, x, zero, &lt, &eq, &gt);
  x_neg_cond->aig[0] = lt;
  release_aig (table, eq);
  release_aig (table, gt);
  ripple_compare_aig_vector (table, y, zero, &lt, &eq, &gt);
  y_neg_cond->aig[0] = lt;
  release_aig (table, eq);
  release_aig (table, gt);
  x_neg = twos_complement_aig_vector (table, x);
  y_neg = twos_complement_aig_vector (table, y);
  *quotient = if_then_else_aig_vector (table, x_neg_cond, x_neg, x);
  *remainder = create_aig_vector ();
  divisor_neg = if_then_else_aig_vector (table, y_neg_cond, y, y_neg);
  for (i = 0; i < ext_number_of_bits; i++)
    {
      /* shift register pair */
      temp = shift_n_bits_left_aig_vector (table, *remainder, 1, AIG_TRUE);
      release_aig_vector (table, *remainder);
      delete_aig_vector (*remainder);
      *remainder = temp;
      assert ((*remainder)->aig[0] == AIG_FALSE);
      (*remainder)->aig[0] =
        copy_aig (table, (*quotient)->aig[ext_number_of_bits - 1]);
      temp = shift_n_bits_left_aig_vector (table, *quotient, 1, AIG_TRUE);
      release_aig_vector (table, *quotient);
      delete_aig_vector (*quotient);
      *quotient = temp;
      /* subtract */
      subtraction_result = add_aig_vector (table, *remainder, divisor_neg);
      ripple_compare_aig_vector (table, subtraction_result, zero, &lt, &eq,
                                 &gt);
      subtraction_result_neg_cond = create_aig_vector ();
      subtraction_result_neg_cond->aig[0] = lt;
      release_aig (table, eq);
      release_aig (table, gt);
      /* compute quotient */
      assert ((*quotient)->aig[0] == AIG_FALSE);
      quotient_temp = copy_aig_vector (table, *quotient);
      quotient_temp->aig[0] = AIG_TRUE;
      temp =
        if_then_else_aig_vector (table, subtraction_result_neg_cond,
                                 *quotient, quotient_temp);
      release_aig_vector (table, *quotient);
      delete_aig_vector (*quotient);
      *quotient = temp;
      /* restore ? */
      temp =
        if_then_else_aig_vector (table, subtraction_result_neg_cond,
                                 *remainder, subtraction_result);
      release_aig_vector (table, *remainder);
      delete_aig_vector (*remainder);
      *remainder = temp;
      /* clean up */
      release_aig_vector (table, subtraction_result);
      release_aig_vector (table, subtraction_result_neg_cond);
      release_aig_vector (table, quotient_temp);
      delete_aig_vector (subtraction_result);
      delete_aig_vector (subtraction_result_neg_cond);
      delete_aig_vector (quotient_temp);
    }
  /* sign quotient and remainder if necessary */
  quotient_neg = twos_complement_aig_vector (table, *quotient);
  quotient_neg_cond = create_aig_vector ();
  quotient_neg_cond->aig[0] =
    xor_aig (table, x_neg_cond->aig[0], y_neg_cond->aig[0]);
  temp =
    if_then_else_aig_vector (table, quotient_neg_cond, quotient_neg,
                             *quotient);
  release_aig_vector (table, *quotient);
  delete_aig_vector (*quotient);
  *quotient = temp;
  remainder_neg = twos_complement_aig_vector (table, *remainder);
  temp =
    if_then_else_aig_vector (table, x_neg_cond, remainder_neg, *remainder);
  release_aig_vector (table, *remainder);
  delete_aig_vector (*remainder);
  *remainder = temp;
  /* cleanup */
  release_aig_vector (table, x_neg_cond);
  release_aig_vector (table, y_neg_cond);
  release_aig_vector (table, x_neg);
  release_aig_vector (table, y_neg);
  release_aig_vector (table, divisor_neg);
  release_aig_vector (table, quotient_neg);
  release_aig_vector (table, remainder_neg);
  release_aig_vector (table, quotient_neg_cond);
  delete_aig_vector (x_neg_cond);
  delete_aig_vector (y_neg_cond);
  delete_aig_vector (x_neg);
  delete_aig_vector (y_neg);
  delete_aig_vector (divisor_neg);
  delete_aig_vector (quotient_neg);
  delete_aig_vector (remainder_neg);
  delete_aig_vector (quotient_neg_cond);
  delete_aig_vector (zero);
}

AIGVector *
divide_aig_vector (AIGUniqueTable ** table, AIGVector * x, AIGVector * y)
{
  AIGVector *quotient = NULL;
  AIGVector *remainder = NULL;
  AIG *temp1 = NULL;
  AIG *temp2 = NULL;
  AIG *temp3 = NULL;
  AIG *int_min = NULL;
  AIG *minus_one = NULL;
  AIG *temp4 = NULL;
  AIGVector *int_min_zeros = NULL;
  int i = 0;
  assert (table != NULL && *table != NULL && x != NULL && y != NULL);
  divide_and_remainder_aig_vector (table, x, y, &quotient, &remainder);
  release_aig_vector (table, remainder);
  delete_aig_vector (remainder);
  int_min_zeros = create_aig_vector ();
  temp1 = or_aig (table, x->undefined, y->undefined);
  /* x / 0 is undefined */
  temp2 = invert_aig (disjunction_aig_vector (table, y));
  /* INT_MIN / -1 is undefined ----> overflow */
  for (i = 0; i < ext_number_of_bits - 1; i++)
    {
      int_min_zeros->aig[i] = x->aig[i];
    }
  assert (int_min_zeros->aig[ext_number_of_bits - 1] == AIG_FALSE);
  temp3 = invert_aig (disjunction_aig_vector (table, int_min_zeros));
  int_min = and_aig (table, x->aig[ext_number_of_bits - 1], temp3);
  minus_one = conjunction_aig_vector (table, y);
  temp4 = and_aig (table, int_min, minus_one);
  release_aig (table, quotient->undefined);
  if (ext_allow_overflow)
    {
      quotient->undefined = or_aig (table, temp1, temp2);
    }
  else
    {
      quotient->undefined = or_aig_va_list (table, 3, temp1, temp2, temp4);
    }
  release_aig (table, temp1);
  release_aig (table, temp2);
  release_aig (table, temp3);
  release_aig (table, int_min);
  release_aig (table, minus_one);
  release_aig (table, temp4);
  delete_aig_vector (int_min_zeros);
  return quotient;
}

AIGVector *
modulo_aig_vector (AIGUniqueTable ** table, AIGVector * x, AIGVector * y)
{
  AIGVector *quotient = NULL;
  AIGVector *remainder = NULL;
  AIG *temp1 = NULL;
  AIG *temp2 = NULL;
  assert (table != NULL && *table != NULL && x != NULL && y != NULL);
  divide_and_remainder_aig_vector (table, x, y, &quotient, &remainder);
  release_aig_vector (table, quotient);
  delete_aig_vector (quotient);
  temp1 = or_aig (table, x->undefined, y->undefined);
  /* x % 0 is undefined */
  temp2 = invert_aig (disjunction_aig_vector (table, y));
  release_aig (table, remainder->undefined);
  remainder->undefined = or_aig (table, temp1, temp2);
  release_aig (table, temp1);
  release_aig (table, temp2);
  return remainder;
}
