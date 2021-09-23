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
#include "test_logging.h"
#include "aig_id_generation_test.h"
#include "../aig.h"
#include "../aig_id_generation.h"
#include "../error_management.h"
#include "../memory_management.h"

void
test_retrieve_aig_id ()
{
  AIGUniqueTable *table = NULL;
  AIG *var1 = NULL;
  AIG *var2 = NULL;
  AIG *var3 = NULL;
  AIG *and1 = NULL;
  AIG *and2 = NULL;
  init_error_management (stderr);
  init_memory_management ();
  table = create_aig_unique_table (8);
  var1 = var_aig (&table, 1);
  var2 = var_aig (&table, 2);
  var3 = var_aig (&table, 3);
  init_aig_id_generation (4);
  assert (retrieve_aig_id (var1) == 1);
  assert (retrieve_aig_id (invert_aig (var1)) == -1);
  assert (retrieve_aig_id (var2) == 2);
  assert (retrieve_aig_id (invert_aig (var2)) == -2);
  assert (retrieve_aig_id (var3) == 3);
  assert (retrieve_aig_id (invert_aig (var3)) == -3);
  and1 = and_aig (&table, var1, var2);
  assert (and1->id == 0);
  assert (retrieve_aig_id (and1) == 4);
  assert (and1->id == 4);
  assert (retrieve_aig_id (invert_aig (and1)) == -4);
  assert (and1->id == 4);
  and2 = and_aig (&table, var1, var3);
  assert (and2->id == 0);
  assert (retrieve_aig_id (and2) == 5);
  assert (and2->id == 5);
  assert (retrieve_aig_id (invert_aig (and2)) == -5);
  assert (and2->id == 5);
  assert (retrieve_aig_id (and1) == 4);
  release_aig (&table, var1);
  release_aig (&table, var2);
  release_aig (&table, var3);
  release_aig (&table, and1);
  release_aig (&table, and2);
  delete_aig_unique_table (table, b_false);
  finalise_memory_management ();
}

void
test_get_next_free_aig_id ()
{
  AIGUniqueTable *table = NULL;
  AIG *var1 = NULL;
  AIG *var2 = NULL;
  AIG *var3 = NULL;
  AIG *and = NULL;
  init_error_management (stderr);
  init_memory_management ();
  table = create_aig_unique_table (8);
  var1 = var_aig (&table, 1);
  var2 = var_aig (&table, 2);
  var3 = var_aig (&table, 3);
  init_aig_id_generation (4);
  assert (get_next_free_aig_id () == 4);
  and = and_aig (&table, var1, var2);
  assert (get_next_free_aig_id () == 4);
  retrieve_aig_id (and);
  assert (get_next_free_aig_id () == 5);
  retrieve_aig_id (and);
  assert (get_next_free_aig_id () == 5);
  release_aig (&table, var1);
  release_aig (&table, var2);
  release_aig (&table, var3);
  release_aig (&table, and);
  delete_aig_unique_table (table, b_false);
  finalise_memory_management ();
}

void
run_aig_id_generation_tests ()
{
  run_test (test_retrieve_aig_id);
  run_test (test_get_next_free_aig_id);
}
