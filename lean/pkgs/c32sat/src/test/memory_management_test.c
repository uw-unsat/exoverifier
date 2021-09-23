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
#include <string.h>
#include <stdio.h>
#include "memory_management_test.h"
#include "test_logging.h"
#include "../memory_management.h"
#include "../error_management.h"
#include "../token.h"
#include "../scanner.h"
#include "../parser.h"
#include "../parse_tree.h"
#include "../aig.h"
#include "../bool.h"

void
test_init_finalise_memory_management ()
{
  init_error_management (stderr);
  assert (!is_initialised_memory_management ());
  init_memory_management ();
  assert (is_initialised_memory_management ());
  finalise_memory_management ();
  assert (!is_initialised_memory_management ());
}

void
test_malloc_realloc_free_c32sat ()
{
  int *x = NULL;
  const int size = 1000;
  int i = 0;
  init_error_management (stderr);
  init_memory_management ();
  x = (int *) malloc_c32sat (sizeof (int));
  assert (x != NULL);
  *x = 3;
  x = (int *) realloc_c32sat (x, sizeof (int), sizeof (int) * size);
  assert (x != NULL);
  for (i = 0; i < size; i++)
    {
      x[i] = i;
    }
  free_c32sat (x, sizeof (int) * size);
  finalise_memory_management ();
}

void
test_get_max_memory_used ()
{
  int *x = NULL;
  init_error_management (stderr);
  init_memory_management ();
  x = (int *) malloc_c32sat (sizeof (int));
  assert (get_max_memory_used () == sizeof (int));
  free_c32sat (x, sizeof (int));
  finalise_memory_management ();
}

void
run_memory_management_tests ()
{
  run_test (test_init_finalise_memory_management);
  run_test (test_malloc_realloc_free_c32sat);
  run_test (test_get_max_memory_used);
}
