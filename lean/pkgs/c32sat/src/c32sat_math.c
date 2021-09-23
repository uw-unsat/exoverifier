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
#include "c32sat_math.h"
#include "bool.h"
#include "config.h"
#include "memory_management.h"

int
log2_c32sat_math (int x)
{
  int result = 0;
  assert (x > 0);
  while (x > 1)
    {
      x >>= 1;
      result++;
    }
  assert (result >= 0);
  return result;
}

long long int
pow2_c32sat_math (int exp)
{
  long long int result = 1;
  assert (exp >= 0);
  while (exp > 0)
    {
      result <<= 1;
      exp--;
    }
  assert (result >= 0);
  return result;
}

unsigned long long int
pow10_ull_c32sat_math (int x)
{
  unsigned long long int result = 1;
  assert (x >= 0);
  while (x > 0)
    {
      result *= 10;
      x--;
    }
  return result;
}

static void
flip_bits (int *bin, int number_of_bits)
{
  int i = 0;
  assert (bin != NULL
          && (number_of_bits == 4
              || number_of_bits == 8 || number_of_bits == 16
              || number_of_bits == 32 || number_of_bits == 64));
  for (i = 0; i < number_of_bits; i++)
    {
      bin[i] = bin[i] ? 0 : 1;
    }
}

long long int
bin_2_long_long_c32sat_math (const int *bin, int number_of_bits)
{
  int i = 0;
  long long int result = 0;
  Bool neg = b_false;
  int bin_temp[number_of_bits];
  assert (bin != NULL
          && (number_of_bits == 4
              || number_of_bits == 8 || number_of_bits == 16
              || number_of_bits == 32 || number_of_bits == 64));
  for (i = 0; i < number_of_bits; i++)
    {
      bin_temp[i] = bin[i] ? 1 : 0;
    }
  if (bin_temp[number_of_bits - 1])
    {
      neg = b_true;
      flip_bits (bin_temp, number_of_bits);
    }
  for (i = 0; i < number_of_bits - 1; i++)
    {
      if (bin_temp[i])
        {
          result += pow2_c32sat_math (i);
        }
    }
  if (neg)
    {
      if (result == LONG_LONG_MAX_VAL)
        {
          result = LONG_LONG_MIN_VAL;
        }
      else
        {
          result++;
          result = -result;
        }
      assert (result < 0);
    }
  else
    {
      assert (result >= 0);
    }
  return result;
}

void
long_long_2_bin_c32sat_math (long long int x, int *result, int number_of_bits)
{
  int i = 0;
  Bool neg = b_false;
  assert (result != NULL
          && (number_of_bits == 4 || number_of_bits == 8
              || number_of_bits == 16 || number_of_bits == 32
              || number_of_bits == 64));
  if (x == LONG_LONG_MIN_VAL)
    {
      result[number_of_bits - 1] = 1;
      for (i = 0; i < number_of_bits - 1; i++)
        {
          result[i] = 0;
        }
    }
  else
    {
      if (x < 0)
        {
          neg = b_true;
          x = -x;
        }
      for (i = 0; i < number_of_bits; i++)
        {
          result[i] = (int) x % 2;
          x >>= 1;
        }
      if (neg)
        {
          flip_bits (result, number_of_bits);
          /* add one  */
          for (i = 0; i < number_of_bits; i++)
            {
              if (result[i])
                {
                  result[i] = 0;
                }
              else
                {
                  result[i] = 1;
                  break;
                }
            }
        }
    }
}

char *
bin_2_hex_c32sat_math (const int *bin, int number_of_bits)
{
  int i = 0;
  int hex_size = 0;
  int pos = 0;
  char *result = NULL;
  assert (bin != NULL
          && (number_of_bits == 4
              || number_of_bits == 8 || number_of_bits == 16
              || number_of_bits == 32 || number_of_bits == 64));
  assert (number_of_bits % 4 == 0);
  hex_size = number_of_bits / 4;
  result = (char *) malloc_c32sat (sizeof (char) * (hex_size + 1));
  i = 0;
  for (pos = hex_size - 1; pos >= 0; pos--)
    {
      assert (i + 3 < number_of_bits);
      if (bin[i + 3] == 0)
        {
          if (bin[i + 2] == 0)
            {
              if (bin[i + 1] == 0)
                {
                  if (bin[i] == 0)
                    {
                      result[pos] = '0';
                    }
                  else
                    {
                      result[pos] = '1';
                    }
                }
              else
                {
                  if (bin[i] == 0)
                    {
                      result[pos] = '2';
                    }
                  else
                    {
                      result[pos] = '3';
                    }
                }
            }
          else
            {
              if (bin[i + 1] == 0)
                {
                  if (bin[i] == 0)
                    {
                      result[pos] = '4';
                    }
                  else
                    {
                      result[pos] = '5';
                    }
                }
              else
                {
                  if (bin[i] == 0)
                    {
                      result[pos] = '6';
                    }
                  else
                    {
                      result[pos] = '7';
                    }
                }
            }
        }
      else
        {
          if (bin[i + 2] == 0)
            {
              if (bin[i + 1] == 0)
                {
                  if (bin[i] == 0)
                    {
                      result[pos] = '8';
                    }
                  else
                    {
                      result[pos] = '9';
                    }
                }
              else
                {
                  if (bin[i] == 0)
                    {
                      result[pos] = 'A';
                    }
                  else
                    {
                      result[pos] = 'B';
                    }
                }
            }
          else
            {
              if (bin[i + 1] == 0)
                {
                  if (bin[i] == 0)
                    {
                      result[pos] = 'C';
                    }
                  else
                    {
                      result[pos] = 'D';
                    }
                }
              else
                {
                  if (bin[i] == 0)
                    {
                      result[pos] = 'E';
                    }
                  else
                    {
                      result[pos] = 'F';
                    }
                }
            }

        }
      i += 4;
    }
  result[hex_size] = 0;
  return result;
}
