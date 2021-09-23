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
#include "aig_2_cnf_transformation_standard_tseitin_test.h"
#include "test_logging.h"
#include "../cnf.h"
#include "../aig.h"
#include "../aig_transformation.h"
#include "../aig_2_cnf_transformation_standard_tseitin.h"
#include "../error_management.h"
#include "../memory_management.h"

void
check_cnf_result (CNF * cnf, int *expected, int size)
{
  int i = 0;
  CNFIterator *cnf_iterator = create_cnf_iterator (cnf);
  for (i = 0; i < size; i++)
    {
      assert (has_next_cnf_iterator (cnf_iterator));
      assert (expected[i] == next_cnf_iterator (cnf_iterator));
    }
  assert (!has_next_cnf_iterator (cnf_iterator));
  delete_cnf_iterator (cnf_iterator);
}

void
test_transform_aig_2_cnf_standard_tseitin_x1_and_x2 ()
{
  AIG *aig = NULL;
  AIGUniqueTable *unique_table = NULL;
  CNF *cnf = NULL;
  int expected[] = { 3, 0, -3, 1, 0, -3, 2, 0, -1, -2, 3, 0
  };
  const int expected_size = 12;
  init_error_management (stderr);
  init_memory_management ();
  unique_table = create_aig_unique_table (8);
  aig =
    and_aig (&unique_table, var_aig (&unique_table, 1),
             var_aig (&unique_table, 2));
  cnf = aig_2_cnf_standard_tseitin (aig, 3);
  check_cnf_result (cnf, expected, expected_size);
  delete_cnf (cnf);
  delete_aig_unique_table (unique_table, b_true);
  finalise_memory_management ();
}

void
test_transform_aig_2_cnf_standard_tseitin_not_x1_and_x2 ()
{
  AIG *aig = NULL;
  AIGUniqueTable *unique_table = NULL;
  CNF *cnf = NULL;
  int expected[] = { 3, 0,
    -3, -1, 0, -3, 2, 0, 1, -2, 3, 0
  };
  const int expected_size = 12;
  init_error_management (stderr);
  init_memory_management ();
  unique_table = create_aig_unique_table (8);
  aig =
    and_aig (&unique_table, invert_aig (var_aig (&unique_table, 1)),
             var_aig (&unique_table, 2));
  cnf = aig_2_cnf_standard_tseitin (aig, 3);
  check_cnf_result (cnf, expected, expected_size);
  delete_cnf (cnf);
  delete_aig_unique_table (unique_table, b_true);
  finalise_memory_management ();
}

void
test_transform_aig_2_cnf_standard_tseitin_x1_and_not_x2 ()
{
  AIG *aig = NULL;
  AIGUniqueTable *unique_table = NULL;
  CNF *cnf = NULL;
  int expected[] = { 3, 0,
    -3, 1, 0, -3, -2, 0, -1, 2, 3, 0
  };
  const int expected_size = 12;
  init_error_management (stderr);
  init_memory_management ();
  unique_table = create_aig_unique_table (8);
  aig =
    and_aig (&unique_table, var_aig (&unique_table, 1),
             invert_aig (var_aig (&unique_table, 2)));
  cnf = aig_2_cnf_standard_tseitin (aig, 3);
  check_cnf_result (cnf, expected, expected_size);
  delete_cnf (cnf);
  delete_aig_unique_table (unique_table, b_true);
  finalise_memory_management ();
}

void
test_transform_aig_2_cnf_standard_tseitin_not_x1_and_not_x2 ()
{
  AIG *aig = NULL;
  AIGUniqueTable *unique_table = NULL;
  CNF *cnf = NULL;
  int expected[] = { 3, 0,
    -3, -1, 0, -3, -2, 0, 1, 2, 3, 0
  };
  const int expected_size = 12;
  init_error_management (stderr);
  init_memory_management ();
  unique_table = create_aig_unique_table (8);
  aig =
    and_aig (&unique_table, invert_aig (var_aig (&unique_table, 1)),
             invert_aig (var_aig (&unique_table, 2)));
  cnf = aig_2_cnf_standard_tseitin (aig, 3);
  check_cnf_result (cnf, expected, expected_size);
  delete_cnf (cnf);
  delete_aig_unique_table (unique_table, b_true);
  finalise_memory_management ();
}

void
test_transform_aig_2_cnf_standard_tseitin_x1_nand_x2 ()
{
  AIG *aig = NULL;
  AIGUniqueTable *unique_table = NULL;
  CNF *cnf = NULL;
  int expected[] = { -3, 0,
    -3, 1, 0, -3, 2, 0, -1, -2, 3, 0
  };
  const int expected_size = 12;
  init_error_management (stderr);
  init_memory_management ();
  unique_table = create_aig_unique_table (8);
  aig =
    invert_aig (and_aig
                (&unique_table, var_aig (&unique_table, 1),
                 var_aig (&unique_table, 2)));
  cnf = aig_2_cnf_standard_tseitin (aig, 3);
  check_cnf_result (cnf, expected, expected_size);
  delete_cnf (cnf);
  delete_aig_unique_table (unique_table, b_true);
  finalise_memory_management ();
}

void
test_transform_aig_2_cnf_standard_tseitin_not_x1_nand_x2 ()
{
  AIG *aig = NULL;
  AIGUniqueTable *unique_table = NULL;
  CNF *cnf = NULL;
  int expected[] = { -3, 0, -3, -1, 0, -3, 2, 0, 1, -2, 3, 0
  };
  const int expected_size = 12;
  init_error_management (stderr);
  init_memory_management ();
  unique_table = create_aig_unique_table (8);
  aig =
    invert_aig (and_aig
                (&unique_table, invert_aig (var_aig (&unique_table, 1)),
                 var_aig (&unique_table, 2)));
  cnf = aig_2_cnf_standard_tseitin (aig, 3);
  check_cnf_result (cnf, expected, expected_size);
  delete_cnf (cnf);
  delete_aig_unique_table (unique_table, b_true);
  finalise_memory_management ();
}

void
test_transform_aig_2_cnf_standard_tseitin_x1_nand_not_x2 ()
{
  AIG *aig = NULL;
  AIGUniqueTable *unique_table = NULL;
  CNF *cnf = NULL;
  int expected[] = { -3, 0,
    -3, 1, 0, -3, -2, 0, -1, 2, 3, 0
  };
  const int expected_size = 12;
  init_error_management (stderr);
  init_memory_management ();
  unique_table = create_aig_unique_table (8);
  aig =
    invert_aig (and_aig
                (&unique_table, var_aig (&unique_table, 1),
                 invert_aig (var_aig (&unique_table, 2))));
  cnf = aig_2_cnf_standard_tseitin (aig, 3);
  check_cnf_result (cnf, expected, expected_size);
  delete_cnf (cnf);
  delete_aig_unique_table (unique_table, b_true);
  finalise_memory_management ();
}

void
test_transform_aig_2_cnf_standard_tseitin_not_x1_nand_not_x2 ()
{
  AIG *aig = NULL;
  AIGUniqueTable *unique_table = NULL;
  CNF *cnf = NULL;
  int expected[] = { -3, 0,
    -3, -1, 0, -3, -2, 0, 1, 2, 3, 0
  };
  const int expected_size = 12;
  init_error_management (stderr);
  init_memory_management ();
  unique_table = create_aig_unique_table (8);
  aig =
    invert_aig (and_aig
                (&unique_table, invert_aig (var_aig (&unique_table, 1)),
                 invert_aig (var_aig (&unique_table, 2))));
  cnf = aig_2_cnf_standard_tseitin (aig, 3);
  check_cnf_result (cnf, expected, expected_size);
  delete_cnf (cnf);
  delete_aig_unique_table (unique_table, b_true);
  finalise_memory_management ();
}

void
run_aig_2_cnf_transformation_standard_tseitin_tests ()
{

  run_test (test_transform_aig_2_cnf_standard_tseitin_x1_and_x2);
  run_test (test_transform_aig_2_cnf_standard_tseitin_not_x1_and_x2);
  run_test (test_transform_aig_2_cnf_standard_tseitin_x1_and_not_x2);
  run_test (test_transform_aig_2_cnf_standard_tseitin_not_x1_and_not_x2);
  run_test (test_transform_aig_2_cnf_standard_tseitin_x1_nand_x2);
  run_test (test_transform_aig_2_cnf_standard_tseitin_not_x1_nand_x2);
  run_test (test_transform_aig_2_cnf_standard_tseitin_x1_nand_not_x2);
  run_test (test_transform_aig_2_cnf_standard_tseitin_not_x1_nand_not_x2);
}
