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
#include <string.h>
#include <stdlib.h>
#include <assert.h>
#include <stdio.h>
#include <errno.h>
#include "exit_codes.h"
#include "bool.h"
#include "c32sat_math.h"
#include "memory_management.h"
#include "error_management.h"

size_t g_allocated_mem;
size_t g_max_allocated_mem;
Bool g_initialised_memory_management = b_false;

static void
out_of_memory ()
{
  error (e_memory_management_out_of_memory, 0, 0, 0, NULL);
  exit (ec_out_of_memory);
}

void
init_memory_management ()
{
  assert (is_initialised_error_management ()
          && !is_initialised_memory_management ());

  g_allocated_mem = 0;
  g_max_allocated_mem = 0;
  g_initialised_memory_management = b_true;
}

Bool
is_initialised_memory_management ()
{
  return g_initialised_memory_management;
}

void *
malloc_c32sat (size_t num_bytes)
{
  void *result = NULL;
  int errno_temp = 0;
  assert (is_initialised_memory_management ());
  errno_temp = errno;
  errno = 0;
  result = malloc (num_bytes);
  if (errno != 0 || result == NULL)
    {
      out_of_memory ();
    }
  errno = errno_temp;
  g_allocated_mem += num_bytes;
  g_max_allocated_mem =
    max_c32sat_math (g_max_allocated_mem, g_allocated_mem);
  return result;
}

void *
realloc_c32sat (void *ptr, size_t old_num_bytes, size_t num_bytes)
{
  void *result = NULL;
  int errno_temp = 0;
  assert (ptr != NULL && is_initialised_memory_management ());
  errno_temp = errno;
  errno = 0;
  assert (g_allocated_mem >= old_num_bytes);
  g_allocated_mem -= old_num_bytes;
  result = realloc (ptr, num_bytes);
  if (errno != 0 || result == NULL)
    {
      out_of_memory ();
    }
  errno = errno_temp;
  g_allocated_mem += num_bytes;
  g_max_allocated_mem =
    max_c32sat_math (g_max_allocated_mem, g_allocated_mem);
  return result;
}

void
free_c32sat (void *ptr, size_t num_bytes_freed)
{
  assert (is_initialised_memory_management () && ptr != NULL);
  assert (g_allocated_mem >= num_bytes_freed);
  g_allocated_mem -= num_bytes_freed;
#ifndef NDEBUG
  memset (ptr, 0, num_bytes_freed);
#endif
  free (ptr);
}

void
finalise_memory_management ()
{
  assert (is_initialised_memory_management ());
  assert (g_allocated_mem == 0);
  g_initialised_memory_management = b_false;
}

long long int
get_max_memory_used ()
{
  assert (is_initialised_memory_management ());
  return (long long int) g_max_allocated_mem;
}
