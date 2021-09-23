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
#include "special_operator.h"
#include "../c32sat_math.h"
#include "../bool.h"

void
shift_left_n_bits_special_operator (int *x, const int number_of_bits,
                                    const int shift)
{
  int i = 0;
  assert (x != NULL && number_of_bits > 0 && shift > 0);
  for (i = number_of_bits - 1; i >= shift; i--)
    {
      x[i] = x[i - shift];
    }
  for (i = 0; i < shift; i++)
    {
      x[i] = 0;
    }
}

void
shift_right_n_bits_special_operator (int *x, const int number_of_bits,
                                     const int shift)
{
  int i = 0;
  int neg = 0;
  assert (x != NULL && number_of_bits > 0 && shift > 0);
  neg = x[number_of_bits - 1] == 1;
  for (i = 0; i < number_of_bits - shift; i++)
    {
      x[i] = x[i + shift];
    }
  for (i = number_of_bits - shift; i < number_of_bits; i++)
    {
      x[i] = neg ? 1 : 0;
    }
}

int
shift_left_special_operator (const int x, const int y,
                             const int number_of_bits)
{
  int i = 0;
  int x_bits[number_of_bits];
  int y_bits[number_of_bits];
  int shift_bits = 1;
  assert (number_of_bits > 0);
  long_long_2_bin_c32sat_math (x, x_bits, number_of_bits);
  long_long_2_bin_c32sat_math (y, y_bits, number_of_bits);
  for (i = 0; i < log2_c32sat_math (number_of_bits); i++)
    {
      if (y_bits[i])
        {
          shift_left_n_bits_special_operator (x_bits, number_of_bits,
                                              shift_bits);
        }
      shift_bits <<= 1;
    }
  return (int) bin_2_long_long_c32sat_math (x_bits, number_of_bits);
}

int
shift_right_special_operator (const int x, const int y,
                              const int number_of_bits)
{
  int i = 0;
  int x_bits[number_of_bits];
  int y_bits[number_of_bits];
  int shift_bits = 1;
  assert (number_of_bits > 0);
  long_long_2_bin_c32sat_math (x, x_bits, number_of_bits);
  long_long_2_bin_c32sat_math (y, y_bits, number_of_bits);
  for (i = 0; i < log2_c32sat_math (number_of_bits); i++)
    {
      if (y_bits[i])
        {
          shift_right_n_bits_special_operator (x_bits, number_of_bits,
                                               shift_bits);
        }
      shift_bits <<= 1;
    }
  return (int) bin_2_long_long_c32sat_math (x_bits, number_of_bits);
}

void
full_add_special_operator (int x, int y, int cin, int *result, int *cout)
{
  assert (result != NULL && cout != NULL);
  *result = x ^ y ^ cin;
  *cout = (y & cin) | (x & cin) | (x & y);
}

void
binary_add_special_operator (const int *x, const int *y, int *result,
                             const int number_of_bits)
{
  int i = 0;
  int cin = 0;
  int cout = 0;
  assert (x != NULL && y != NULL && result != NULL && number_of_bits > 0);
  for (i = 0; i < number_of_bits; i++)
    {
      full_add_special_operator (x[i], y[i], cin, result + i, &cout);
      cin = cout;
    }
}

int
add_special_operator (const int x, const int y, const int number_of_bits)
{
  int x_bits[number_of_bits];
  int y_bits[number_of_bits];
  int result_bits[number_of_bits];
  assert (number_of_bits > 0);
  long_long_2_bin_c32sat_math (x, x_bits, number_of_bits);
  long_long_2_bin_c32sat_math (y, y_bits, number_of_bits);
  binary_add_special_operator (x_bits, y_bits, result_bits, number_of_bits);
  return (int) bin_2_long_long_c32sat_math (result_bits, number_of_bits);
}

void
twos_complement_special_operator (int *x, int *result, int number_of_bits)
{
  int one_bits[number_of_bits];
  int i = 0;
  assert (x != NULL && result != NULL && number_of_bits > 0);
  long_long_2_bin_c32sat_math (1, one_bits, number_of_bits);
  for (i = 0; i < number_of_bits; i++)
    {
      x[i] = x[i] ? 0 : 1;
    }
  binary_add_special_operator (x, one_bits, result, number_of_bits);
}

int
subtract_special_operator (const int x, const int y, const int number_of_bits)
{
  int x_bits[number_of_bits];
  int y_bits[number_of_bits];
  int y_bits_comp[number_of_bits];
  int result_bits[number_of_bits];
  assert (number_of_bits > 0);
  long_long_2_bin_c32sat_math (x, x_bits, number_of_bits);
  long_long_2_bin_c32sat_math (y, y_bits, number_of_bits);
  twos_complement_special_operator (y_bits, y_bits_comp, number_of_bits);
  binary_add_special_operator (x_bits, y_bits_comp, result_bits,
                               number_of_bits);
  return (int) bin_2_long_long_c32sat_math (result_bits, number_of_bits);
}

int
multiply_special_operator (const int x, const int y, const int number_of_bits)
{
  int x_bits[number_of_bits];
  int y_bits[number_of_bits];
  int result_bits[number_of_bits];
  int temp_bits[number_of_bits];
  int i = 0;
  int j = 0;
  assert (number_of_bits > 0);
  long_long_2_bin_c32sat_math (x, x_bits, number_of_bits);
  long_long_2_bin_c32sat_math (y, y_bits, number_of_bits);
  for (i = 0; i < number_of_bits; i++)
    {
      result_bits[i] = 0;
    }
  for (i = 0; i < number_of_bits; i++)
    {
      if (y_bits[i])
        {
          binary_add_special_operator (x_bits, result_bits, temp_bits,
                                       number_of_bits);
          for (j = 0; j < number_of_bits; j++)
            {
              result_bits[j] = temp_bits[j];
            }
        }
      shift_left_n_bits_special_operator (x_bits, number_of_bits, 1);
    }
  return (int) bin_2_long_long_c32sat_math (result_bits, number_of_bits);
}
