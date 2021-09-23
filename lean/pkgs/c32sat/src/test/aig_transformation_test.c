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
#include <string.h>
#include <stdlib.h>
#include "aig_transformation_test.h"
#include "test_logging.h"
#include "../bool.h"
#include "../cnf.h"
#include "../aig.h"
#include "../aig_transformation.h"
#include "../error_management.h"
#include "../memory_management.h"
#include "../aig_2_cnf_transformation_standard_tseitin.h"

void
test_create_delete_aig_2_cnf_transformer ()
{
  AIG2CNFTransformer *transformer = NULL;
  init_error_management (stderr);
  init_memory_management ();
  transformer =
    create_aig_2_cnf_transformer ("aig_2_cnf_standard_tseitin",
                                  aig_2_cnf_standard_tseitin);
  assert (transformer != NULL);
  delete_aig_2_cnf_transformer (transformer);
  finalise_memory_management ();
}

void
test_create_delete_aig_2_cnf_transformers ()
{
  AIG2CNFTransformer **transformers = NULL;
  int size = 0;
  init_error_management (stderr);
  init_memory_management ();
  transformers = create_aig_2_cnf_transformers (&size);
  assert (transformers != NULL);
  assert (size > 0);
  delete_aig_2_cnf_transformers (transformers, size);
  finalise_memory_management ();
}

void
test_transform_aig_2_cnf ()
{
  AIG *and_top = NULL;
  AIG *and_left = NULL;
  AIG *and_right = NULL;
  AIG *x1 = NULL;
  AIG *x2 = NULL;
  AIG *x3 = NULL;
  CNF *cnf = NULL;
  AIGUniqueTable *table = NULL;
  AIG2CNFTransformer *transformer = NULL;
  init_error_management (stderr);
  init_memory_management ();
  table = create_aig_unique_table (8);
  x1 = var_aig (&table, 1);
  x2 = var_aig (&table, 2);
  x3 = var_aig (&table, 3);
  and_left = and_aig (&table, x1, x2);
  and_right = and_aig (&table, x3, and_left);
  and_top = and_aig (&table, and_left, invert_aig (and_right));
  transformer =
    create_aig_2_cnf_transformer ("aig_2_cnf_standard_tseitin",
                                  aig_2_cnf_standard_tseitin);
  cnf = transform_aig_2_cnf (and_top, 4, transformer);
  assert (cnf != NULL);
  delete_cnf (cnf);
  delete_aig_unique_table (table, b_true);
  delete_aig_2_cnf_transformer (transformer);
  finalise_memory_management ();
}

void
run_aig_transformation_tests ()
{
  run_test (test_create_delete_aig_2_cnf_transformer);
  run_test (test_create_delete_aig_2_cnf_transformers);
  run_test (test_transform_aig_2_cnf);
}
