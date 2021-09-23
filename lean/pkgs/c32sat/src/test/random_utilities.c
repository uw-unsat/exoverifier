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
#include <time.h>
#include "random_utilities.h"

static int g_is_initialised_random_utilities = 0;

void
init_random_utilites ()
{
  assert (!is_initialised_random_utilities ());
  srand (time (NULL));
  g_is_initialised_random_utilities = 1;
}

int
is_initialised_random_utilities ()
{
  return g_is_initialised_random_utilities;
}

void
run_void_int_function_random (void (*f_ptr) (int), int times)
{
  int x = 0;
  int i = 0;
  assert (times > 0);
  assert (is_initialised_random_utilities ());
  for (i = 0; i < times; i++)
    {
      x = rand ();
      if (rand () % 2 == 1)
        {
          x = -x;
        }
      f_ptr (x);
    }
}

void
run_void_int_int_function_random (void (*f_ptr) (int, int), int times)
{
  int x = 0;
  int y = 0;
  int i = 0;
  assert (times > 0);
  assert (is_initialised_random_utilities ());
  for (i = 0; i < times; i++)
    {
      x = rand ();
      if (rand () % 2 == 1)
        {
          x = -x;
        }
      y = rand ();
      if (rand () % 2 == 1)
        {
          y = -y;
        }
      f_ptr (x, y);
    }
}

void
run_void_int_int_function_random_second_not_zero (void (*f_ptr) (int, int),
                                                  int times)
{
  int x = 0;
  int y = 0;
  int i = 0;
  assert (times > 0);
  assert (is_initialised_random_utilities ());
  for (i = 0; i < times; i++)
    {
      x = rand ();
      if (rand () % 2 == 1)
        {
          x = -x;
        }
      do
        {
          y = rand ();
        }
      while (y == 0);
      if (rand () % 2 == 1)
        {
          y = -y;
        }
      assert (y != 0);
      f_ptr (x, y);
    }
}

void
run_void_int_int_int_function_random (void (*f_ptr) (int, int, int),
                                      int times)
{
  int x = 0;
  int y = 0;
  int z = 0;
  int i = 0;
  assert (times > 0);
  assert (is_initialised_random_utilities ());
  for (i = 0; i < times; i++)
    {
      x = rand ();
      if (rand () % 2 == 1)
        {
          x = -x;
        }
      y = rand ();
      if (rand () % 2 == 1)
        {
          y = -y;
        }
      z = rand ();
      if (rand () % 2 == 1)
        {
          z = -z;
        }
      f_ptr (x, y, z);
    }
}
