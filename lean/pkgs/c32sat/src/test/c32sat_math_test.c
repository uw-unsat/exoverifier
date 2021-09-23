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
#include <string.h>
#include "c32sat_math_test.h"
#include "test_logging.h"
#include "../c32sat_math.h"
#include "../config.h"
#include "../memory_management.h"
#include "../error_management.h"

void
test_min_c32sat_math ()
{
  assert (min_c32sat_math (3, 4) == 3);
  assert (min_c32sat_math (4, 3) == 3);
  assert (min_c32sat_math (-3, 5) == -3);
  assert (min_c32sat_math (5, -3) == -3);
  assert (min_c32sat_math (0, 0) == 0);
  assert (min_c32sat_math (0, 10) == 0);
  assert (min_c32sat_math (10, 0) == 0);
}

void
test_max_c32sat_math ()
{
  assert (max_c32sat_math (3, 4) == 4);
  assert (max_c32sat_math (4, 3) == 4);
  assert (max_c32sat_math (-3, 5) == 5);
  assert (max_c32sat_math (5, -3) == 5);
  assert (max_c32sat_math (0, 0) == 0);
  assert (max_c32sat_math (0, 10) == 10);
  assert (max_c32sat_math (10, 0) == 10);
}

void
test_log2_c32sat_math ()
{
  assert (log2_c32sat_math (1) == 0);
  assert (log2_c32sat_math (2) == 1);
  assert (log2_c32sat_math (3) == 1);
  assert (log2_c32sat_math (4) == 2);
  assert (log2_c32sat_math (5) == 2);
  assert (log2_c32sat_math (6) == 2);
  assert (log2_c32sat_math (7) == 2);
  assert (log2_c32sat_math (8) == 3);
  assert (log2_c32sat_math (16) == 4);
  assert (log2_c32sat_math (32) == 5);
  assert (log2_c32sat_math (64) == 6);
  assert (log2_c32sat_math (128) == 7);
  assert (log2_c32sat_math (256) == 8);
  assert (log2_c32sat_math (512) == 9);
  assert (log2_c32sat_math (1024) == 10);
}

void
test_pow2_c32sat_math ()
{
  assert (pow2_c32sat_math (0) == 1);
  assert (pow2_c32sat_math (1) == 2);
  assert (pow2_c32sat_math (2) == 4);
  assert (pow2_c32sat_math (3) == 8);
  assert (pow2_c32sat_math (4) == 16);
  assert (pow2_c32sat_math (5) == 32);
  assert (pow2_c32sat_math (6) == 64);
  assert (pow2_c32sat_math (7) == 128);
  assert (pow2_c32sat_math (8) == 256);
  assert (pow2_c32sat_math (9) == 512);
  assert (pow2_c32sat_math (10) == 1024);
  assert (pow2_c32sat_math (11) == 2048);
  assert (pow2_c32sat_math (12) == 4096);
  assert (pow2_c32sat_math (13) == 8192);
  assert (pow2_c32sat_math (14) == 16384);
}

void
test_pow10_ull_c32sat_math ()
{
  assert (pow10_ull_c32sat_math (0) == 1ULL);
  assert (pow10_ull_c32sat_math (1) == 10ULL);
  assert (pow10_ull_c32sat_math (2) == 100ULL);
  assert (pow10_ull_c32sat_math (3) == 1000ULL);
  assert (pow10_ull_c32sat_math (4) == 10000ULL);
  assert (pow10_ull_c32sat_math (5) == 100000ULL);
  assert (pow10_ull_c32sat_math (6) == 1000000ULL);
  assert (pow10_ull_c32sat_math (7) == 10000000ULL);
  assert (pow10_ull_c32sat_math (8) == 100000000ULL);
  assert (pow10_ull_c32sat_math (9) == 1000000000ULL);
  assert (pow10_ull_c32sat_math (10) == 10000000000ULL);
  assert (pow10_ull_c32sat_math (11) == 100000000000ULL);
  assert (pow10_ull_c32sat_math (12) == 1000000000000ULL);
  assert (pow10_ull_c32sat_math (13) == 10000000000000ULL);
  assert (pow10_ull_c32sat_math (14) == 100000000000000ULL);

}

void
clear_bin (int *bin, int number_of_bits)
{
  int i = 0;
  assert (number_of_bits > 2);
  for (i = 0; i < number_of_bits; i++)
    {
      bin[i] = 0;
    }
}

void
test_bin_2_long_long_c32sat_math ()
{
  int i = 0;
  const int bits_64 = 64;
  const int bits_32 = 32;
  const int bits_16 = 16;
  const int bits_8 = 8;
  const int bits_4 = 4;
  int bin_64[bits_64];
  int bin_32[bits_32];
  int bin_16[bits_16];
  int bin_8[bits_8];
  int bin_4[bits_4];
  clear_bin (bin_4, bits_4);
  assert (bin_2_long_long_c32sat_math (bin_4, bits_4) == 0);
  bin_4[0] = 1;
  assert (bin_2_long_long_c32sat_math (bin_4, bits_4) == 1);
  bin_4[0] = 0;
  bin_4[1] = 1;
  assert (bin_2_long_long_c32sat_math (bin_4, bits_4) == 2);
  bin_4[0] = 1;
  assert (bin_2_long_long_c32sat_math (bin_4, bits_4) == 3);
  for (i = 0; i < bits_4; i++)
    {
      bin_4[i] = 1;
    }
  assert (bin_2_long_long_c32sat_math (bin_4, bits_4) == -1);  
  clear_bin (bin_8, bits_8);
  assert (bin_2_long_long_c32sat_math (bin_8, bits_8) == 0);
  bin_8[0] = 1;
  assert (bin_2_long_long_c32sat_math (bin_8, bits_8) == 1);
  bin_8[0] = 0;
  bin_8[1] = 1;
  assert (bin_2_long_long_c32sat_math (bin_8, bits_8) == 2);
  bin_8[0] = 1;
  assert (bin_2_long_long_c32sat_math (bin_8, bits_8) == 3);
  clear_bin (bin_8, bits_8);
  bin_8[7] = 1;
  assert (bin_2_long_long_c32sat_math (bin_8, bits_8) == -128);
  bin_8[0] = 1;
  assert (bin_2_long_long_c32sat_math (bin_8, bits_8) == -127);
  for (i = 0; i < bits_8; i++)
    {
      bin_8[i] = 1;
    }
  assert (bin_2_long_long_c32sat_math (bin_8, bits_8) == -1);
  clear_bin (bin_16, bits_16);
  assert (bin_2_long_long_c32sat_math (bin_16, bits_16) == 0);
  bin_16[0] = 1;
  assert (bin_2_long_long_c32sat_math (bin_16, bits_16) == 1);
  bin_16[0] = 0;
  bin_16[15] = 1;
  assert (bin_2_long_long_c32sat_math (bin_16, bits_16) == -32768);
  bin_16[15] = 0;
  for (i = 0; i < bits_16 - 1; i++)
    {
      bin_16[i] = 1;
    }
  assert (bin_2_long_long_c32sat_math (bin_16, bits_16) == 32767);
  bin_16[15] = 1;
  assert (bin_2_long_long_c32sat_math (bin_16, bits_16) == -1);
  clear_bin (bin_32, bits_32);
  assert (bin_2_long_long_c32sat_math (bin_32, bits_32) == 0);
  bin_32[2] = 1;
  bin_32[4] = 1;
  bin_32[6] = 1;
  assert (bin_2_long_long_c32sat_math (bin_32, bits_32) == 84);
  clear_bin (bin_32, bits_32);
  bin_32[1] = 1;
  bin_32[2] = 1;
  bin_32[3] = 1;
  bin_32[4] = 1;
  bin_32[6] = 1;
  for (i = 11; i < 32; i++)
    {
      bin_32[i] = 1;
    }
  assert (bin_2_long_long_c32sat_math (bin_32, bits_32) == -1954);
  clear_bin (bin_32, bits_32);
  bin_32[3] = 1;
  assert (bin_2_long_long_c32sat_math (bin_32, bits_32) == 8);
  clear_bin (bin_32, bits_32);
  bin_32[1] = 1;
  bin_32[3] = 1;
  bin_32[4] = 1;
  bin_32[5] = 1;
  bin_32[6] = 1;
  bin_32[7] = 1;
  bin_32[9] = 1;
  for (i = 11; i < bits_32; i++)
    {
      bin_32[i] = 1;
    }
  assert (bin_2_long_long_c32sat_math (bin_32, bits_32) == -1286);
  clear_bin (bin_32, bits_32);
  for (i = 0; i < bits_32 - 1; i++)
    {
      bin_32[i] = 1;
    }
  assert (bin_2_long_long_c32sat_math (bin_32, bits_32) == INT_MAX);
  clear_bin (bin_32, bits_32);
  bin_32[31] = 1;
  assert (bin_2_long_long_c32sat_math (bin_32, bits_32) == INT_MIN);
  clear_bin (bin_32, bits_32);
  for (i = 0; i < bits_32; i++)
    {
      bin_32[i] = 1;
    }
  assert (bin_2_long_long_c32sat_math (bin_32, bits_32) == -1);
  clear_bin (bin_32, bits_32);
  bin_32[0] = 1;
  assert (bin_2_long_long_c32sat_math (bin_32, bits_32) == 1);
  clear_bin (bin_64, bits_64);
  assert (bin_2_long_long_c32sat_math (bin_64, bits_64) == 0);
  bin_64[0] = 1;
  assert (bin_2_long_long_c32sat_math (bin_64, bits_64) == 1);
  bin_64[0] = 0;
  bin_64[63] = 1;
  assert (bin_2_long_long_c32sat_math (bin_64, bits_64) == LONG_LONG_MIN_VAL);
  bin_64[63] = 0;
  for (i = 0; i < bits_64 - 1; i++)
    {
      bin_64[i] = 1;
    }
  assert (bin_2_long_long_c32sat_math (bin_64, bits_64) == LONG_LONG_MAX_VAL);
  bin_64[63] = 1;
  assert (bin_2_long_long_c32sat_math (bin_64, bits_64) == -1);
}

void
test_long_long_2_bin_c32sat_math ()
{
  const int bits_64 = 64;
  const int bits_32 = 32;
  const int bits_16 = 16;
  const int bits_8 = 8;
  const int bits_4 = 4;
  int result_64[bits_64];
  int result_32[bits_32];
  int result_16[bits_16];
  int result_8[bits_8];
  int result_4[bits_4];
  long_long_2_bin_c32sat_math (0, result_4, bits_4);
  assert (bin_2_long_long_c32sat_math (result_4, bits_4) == 0);
  long_long_2_bin_c32sat_math (1, result_4, bits_4);
  assert (bin_2_long_long_c32sat_math (result_4, bits_4) == 1);
  long_long_2_bin_c32sat_math (2, result_4, bits_4);
  assert (bin_2_long_long_c32sat_math (result_4, bits_4) == 2);
  long_long_2_bin_c32sat_math (3, result_4, bits_4);
  assert (bin_2_long_long_c32sat_math (result_4, bits_4) == 3);
  long_long_2_bin_c32sat_math (-1, result_4, bits_4);
  assert (bin_2_long_long_c32sat_math (result_4, bits_4) == -1);
  
  long_long_2_bin_c32sat_math (0, result_8, bits_8);
  assert (bin_2_long_long_c32sat_math (result_8, bits_8) == 0);
  long_long_2_bin_c32sat_math (1, result_8, bits_8);
  assert (bin_2_long_long_c32sat_math (result_8, bits_8) == 1);
  long_long_2_bin_c32sat_math (2, result_8, bits_8);
  assert (bin_2_long_long_c32sat_math (result_8, bits_8) == 2);
  long_long_2_bin_c32sat_math (3, result_8, bits_8);
  assert (bin_2_long_long_c32sat_math (result_8, bits_8) == 3);
  long_long_2_bin_c32sat_math (-1, result_8, bits_8);
  assert (bin_2_long_long_c32sat_math (result_8, bits_8) == -1);
  long_long_2_bin_c32sat_math (-2, result_8, bits_8);
  assert (bin_2_long_long_c32sat_math (result_8, bits_8) == -2);
  long_long_2_bin_c32sat_math (-3, result_8, bits_8);
  assert (bin_2_long_long_c32sat_math (result_8, bits_8) == -3);
  long_long_2_bin_c32sat_math (-4, result_8, bits_8);
  assert (bin_2_long_long_c32sat_math (result_8, bits_8) == -4);
  long_long_2_bin_c32sat_math (127, result_8, bits_8);
  assert (bin_2_long_long_c32sat_math (result_8, bits_8) == 127);
  long_long_2_bin_c32sat_math (-128, result_8, bits_8);
  assert (bin_2_long_long_c32sat_math (result_8, bits_8) == -128);

  long_long_2_bin_c32sat_math (0, result_16, bits_16);
  assert (bin_2_long_long_c32sat_math (result_16, bits_16) == 0);
  long_long_2_bin_c32sat_math (1, result_16, bits_16);
  assert (bin_2_long_long_c32sat_math (result_16, bits_16) == 1);
  long_long_2_bin_c32sat_math (2, result_16, bits_16);
  assert (bin_2_long_long_c32sat_math (result_16, bits_16) == 2);
  long_long_2_bin_c32sat_math (3, result_16, bits_16);
  assert (bin_2_long_long_c32sat_math (result_16, bits_16) == 3);
  long_long_2_bin_c32sat_math (-1, result_16, bits_16);
  assert (bin_2_long_long_c32sat_math (result_16, bits_16) == -1);
  long_long_2_bin_c32sat_math (-2, result_16, bits_16);
  assert (bin_2_long_long_c32sat_math (result_16, bits_16) == -2);
  long_long_2_bin_c32sat_math (-3, result_16, bits_16);
  assert (bin_2_long_long_c32sat_math (result_16, bits_16) == -3);
  long_long_2_bin_c32sat_math (-4, result_16, bits_16);
  assert (bin_2_long_long_c32sat_math (result_16, bits_16) == -4);
  long_long_2_bin_c32sat_math (32767, result_16, bits_16);
  assert (bin_2_long_long_c32sat_math (result_16, bits_16) == 32767);
  long_long_2_bin_c32sat_math (-32768, result_16, bits_16);
  assert (bin_2_long_long_c32sat_math (result_16, bits_16) == -32768);

  long_long_2_bin_c32sat_math (0, result_32, bits_32);
  assert (bin_2_long_long_c32sat_math (result_32, bits_32) == 0);
  long_long_2_bin_c32sat_math (1, result_32, bits_32);
  assert (bin_2_long_long_c32sat_math (result_32, bits_32) == 1);
  long_long_2_bin_c32sat_math (2, result_32, bits_32);
  assert (bin_2_long_long_c32sat_math (result_32, bits_32) == 2);
  long_long_2_bin_c32sat_math (3, result_32, bits_32);
  assert (bin_2_long_long_c32sat_math (result_32, bits_32) == 3);
  long_long_2_bin_c32sat_math (-1, result_32, bits_32);
  assert (bin_2_long_long_c32sat_math (result_32, bits_32) == -1);
  long_long_2_bin_c32sat_math (-2, result_32, bits_32);
  assert (bin_2_long_long_c32sat_math (result_32, bits_32) == -2);
  long_long_2_bin_c32sat_math (-3, result_32, bits_32);
  assert (bin_2_long_long_c32sat_math (result_32, bits_32) == -3);
  long_long_2_bin_c32sat_math (-4, result_32, bits_32);
  assert (bin_2_long_long_c32sat_math (result_32, bits_32) == -4);
  long_long_2_bin_c32sat_math (INT_MAX, result_32, bits_32);
  assert (bin_2_long_long_c32sat_math (result_32, bits_32) == INT_MAX);
  long_long_2_bin_c32sat_math (INT_MIN, result_32, bits_32);
  assert (bin_2_long_long_c32sat_math (result_32, bits_32) == INT_MIN);

  long_long_2_bin_c32sat_math (0, result_64, bits_64);
  assert (bin_2_long_long_c32sat_math (result_64, bits_64) == 0);
  long_long_2_bin_c32sat_math (1, result_64, bits_64);
  assert (bin_2_long_long_c32sat_math (result_64, bits_64) == 1);
  long_long_2_bin_c32sat_math (2, result_64, bits_64);
  assert (bin_2_long_long_c32sat_math (result_64, bits_64) == 2);
  long_long_2_bin_c32sat_math (3, result_64, bits_64);
  assert (bin_2_long_long_c32sat_math (result_64, bits_64) == 3);
  long_long_2_bin_c32sat_math (-1, result_64, bits_64);
  assert (bin_2_long_long_c32sat_math (result_64, bits_64) == -1);
  long_long_2_bin_c32sat_math (-2, result_64, bits_64);
  assert (bin_2_long_long_c32sat_math (result_64, bits_64) == -2);
  long_long_2_bin_c32sat_math (-3, result_64, bits_64);
  assert (bin_2_long_long_c32sat_math (result_64, bits_64) == -3);
  long_long_2_bin_c32sat_math (-4, result_64, bits_64);
  assert (bin_2_long_long_c32sat_math (result_64, bits_64) == -4);
  long_long_2_bin_c32sat_math (LONG_LONG_MAX_VAL, result_64, bits_64);
  assert (bin_2_long_long_c32sat_math (result_64, bits_64) ==
          LONG_LONG_MAX_VAL);
  long_long_2_bin_c32sat_math (LONG_LONG_MIN_VAL, result_64, bits_64);
  assert (bin_2_long_long_c32sat_math (result_64, bits_64) ==
          LONG_LONG_MIN_VAL);
}

void
test_bin_2_hex_c32sat_math ()
{
  char *result = NULL;
  int bin_8bits[8] = { 1, 0, 0, 1, 0, 0, 0, 1 };
  int bin_4bits[4] = { 0, 0, 0, 0 };
  int i = 0;
  init_error_management (stderr);
  init_memory_management ();
  result = bin_2_hex_c32sat_math (bin_4bits, 4);
  assert (strcmp (result, "0") == 0);
  free_c32sat (result, sizeof (char) * (strlen (result) + 1));
  bin_4bits[0] = 1;
  result = bin_2_hex_c32sat_math (bin_4bits, 4);
  assert (strcmp (result, "1") == 0);
  free_c32sat (result, sizeof (char) * (strlen (result) + 1));
  bin_4bits[0] = 0;
  bin_4bits[1] = 1;
  result = bin_2_hex_c32sat_math (bin_4bits, 4);
  assert (strcmp (result, "2") == 0);
  free_c32sat (result, sizeof (char) * (strlen (result) + 1));
  bin_4bits[0] = 1;
  result = bin_2_hex_c32sat_math (bin_4bits, 4);
  assert (strcmp (result, "3") == 0);
  free_c32sat (result, sizeof (char) * (strlen (result) + 1));
  bin_4bits[0] = 0;
  bin_4bits[1] = 0;
  bin_4bits[2] = 1;
  result = bin_2_hex_c32sat_math (bin_4bits, 4);
  assert (strcmp (result, "4") == 0);
  free_c32sat (result, sizeof (char) * (strlen (result) + 1));
  bin_4bits[0] = 1;
  result = bin_2_hex_c32sat_math (bin_4bits, 4);
  assert (strcmp (result, "5") == 0);
  free_c32sat (result, sizeof (char) * (strlen (result) + 1));
  bin_4bits[0] = 0;
  bin_4bits[1] = 1;
  result = bin_2_hex_c32sat_math (bin_4bits, 4);
  assert (strcmp (result, "6") == 0);
  free_c32sat (result, sizeof (char) * (strlen (result) + 1));
  bin_4bits[0] = 1;
  result = bin_2_hex_c32sat_math (bin_4bits, 4);
  assert (strcmp (result, "7") == 0);
  free_c32sat (result, sizeof (char) * (strlen (result) + 1));
  bin_4bits[0] = 0;
  bin_4bits[1] = 0;
  bin_4bits[2] = 0;
  bin_4bits[3] = 1;
  result = bin_2_hex_c32sat_math (bin_4bits, 4);
  assert (strcmp (result, "8") == 0);
  free_c32sat (result, sizeof (char) * (strlen (result) + 1));
  bin_4bits[0] = 1;
  result = bin_2_hex_c32sat_math (bin_4bits, 4);
  assert (strcmp (result, "9") == 0);
  free_c32sat (result, sizeof (char) * (strlen (result) + 1));
  bin_4bits[0] = 0;
  bin_4bits[1] = 1;
  result = bin_2_hex_c32sat_math (bin_4bits, 4);
  assert (strcmp (result, "A") == 0);
  free_c32sat (result, sizeof (char) * (strlen (result) + 1));
  bin_4bits[0] = 1;
  result = bin_2_hex_c32sat_math (bin_4bits, 4);
  assert (strcmp (result, "B") == 0);
  free_c32sat (result, sizeof (char) * (strlen (result) + 1));
  bin_4bits[0] = 0;
  bin_4bits[1] = 0;
  bin_4bits[2] = 1;
  result = bin_2_hex_c32sat_math (bin_4bits, 4);
  assert (strcmp (result, "C") == 0);
  free_c32sat (result, sizeof (char) * (strlen (result) + 1));
  bin_4bits[0] = 1;
  result = bin_2_hex_c32sat_math (bin_4bits, 4);
  assert (strcmp (result, "D") == 0);
  free_c32sat (result, sizeof (char) * (strlen (result) + 1));
  bin_4bits[0] = 0;
  bin_4bits[1] = 1;
  result = bin_2_hex_c32sat_math (bin_4bits, 4);
  assert (strcmp (result, "E") == 0);
  free_c32sat (result, sizeof (char) * (strlen (result) + 1));
  bin_4bits[0] = 1;
  result = bin_2_hex_c32sat_math (bin_4bits, 4);
  assert (strcmp (result, "F") == 0);
  free_c32sat (result, sizeof (char) * (strlen (result) + 1));
  result = bin_2_hex_c32sat_math (bin_8bits, 8);
  assert (strcmp (result, "89") == 0);
  free_c32sat (result, sizeof (char) * (strlen (result) + 1));
  for (i = 0; i < 8; i++)
    {
      bin_8bits[i] = 1;
    }
  result = bin_2_hex_c32sat_math (bin_8bits, 8);
  assert (strcmp (result, "FF") == 0);
  free_c32sat (result, sizeof (char) * (strlen (result) + 1));
  bin_8bits[0] = 0;
  result = bin_2_hex_c32sat_math (bin_8bits, 8);
  assert (strcmp (result, "FE") == 0);
  free_c32sat (result, sizeof (char) * (strlen (result) + 1));
  finalise_memory_management ();
}

void
run_c32sat_math_tests ()
{
  run_test (test_min_c32sat_math);
  run_test (test_max_c32sat_math);
  run_test (test_log2_c32sat_math);
  run_test (test_pow2_c32sat_math);
  run_test (test_pow10_ull_c32sat_math);
  run_test (test_bin_2_long_long_c32sat_math);
  run_test (test_long_long_2_bin_c32sat_math);
  run_test (test_bin_2_hex_c32sat_math);
}
