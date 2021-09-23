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
#include <stdlib.h>
#include <stdio.h>
#include "aig_test.h"
#include "test_logging.h"
#include "../aig.h"
#include "../aig_id_generation.h"
#include "../memory_management.h"
#include "../error_management.h"
#include "../bool.h"
#include "../config.h"

const AIG *g_and_aig_3_expected_results[] =
  { AIG_FALSE, AIG_FALSE, AIG_FALSE, AIG_FALSE, AIG_FALSE, AIG_FALSE,
  AIG_FALSE, AIG_TRUE
};
const AIG *g_and_aig_4_expected_results[] =
  { AIG_FALSE, AIG_FALSE, AIG_FALSE, AIG_FALSE, AIG_FALSE, AIG_FALSE,
  AIG_FALSE, AIG_FALSE, AIG_FALSE, AIG_FALSE, AIG_FALSE, AIG_FALSE, AIG_FALSE,
  AIG_FALSE, AIG_FALSE, AIG_TRUE
};

const AIG *g_or_aig_3_expected_results[] =
  { AIG_FALSE, AIG_TRUE, AIG_TRUE, AIG_TRUE, AIG_TRUE, AIG_TRUE, AIG_TRUE,
  AIG_TRUE
};
const AIG *g_or_aig_4_expected_results[] =
  { AIG_FALSE, AIG_TRUE, AIG_TRUE, AIG_TRUE, AIG_TRUE, AIG_TRUE, AIG_TRUE,
  AIG_TRUE, AIG_TRUE, AIG_TRUE, AIG_TRUE, AIG_TRUE, AIG_TRUE, AIG_TRUE,
  AIG_TRUE, AIG_TRUE
};

const AIG *g_dimp_aig_3_expected_results[] =
  { AIG_FALSE, AIG_TRUE, AIG_TRUE, AIG_FALSE, AIG_TRUE, AIG_FALSE, AIG_FALSE,
  AIG_TRUE
};
const AIG *g_dimp_aig_4_expected_results[] =
  { AIG_TRUE, AIG_FALSE, AIG_FALSE, AIG_TRUE, AIG_FALSE, AIG_TRUE, AIG_TRUE,
  AIG_FALSE, AIG_FALSE, AIG_TRUE, AIG_TRUE, AIG_FALSE, AIG_TRUE, AIG_FALSE,
  AIG_FALSE, AIG_TRUE
};

const AIG *g_xor_aig_3_expected_results[] =
  { AIG_FALSE, AIG_TRUE, AIG_TRUE, AIG_FALSE, AIG_TRUE, AIG_FALSE, AIG_FALSE,
  AIG_TRUE
};
const AIG *g_xor_aig_4_expected_results[] =
  { AIG_FALSE, AIG_TRUE, AIG_TRUE, AIG_FALSE, AIG_TRUE, AIG_FALSE, AIG_FALSE,
  AIG_TRUE, AIG_TRUE, AIG_FALSE, AIG_FALSE, AIG_TRUE, AIG_FALSE, AIG_TRUE,
  AIG_TRUE, AIG_FALSE
};

void
test_create_delete_aig_unique_table ()
{
  AIG *aig1 = NULL;
  AIG *aig2 = NULL;
  AIG *aig3 = NULL;
  AIGUniqueTable *table = NULL;
  int i = 0;
  const int power = 20;
  init_error_management (stderr);
  init_memory_management ();
  table = create_aig_unique_table (power);
  assert (table->size == 1 << power);
  assert (table->num_vars == 0);
  assert (table->num_ands == 0);
  assert (table->ref_overflow_occured == b_false);
  assert (table->chains != NULL);
  for (i = 0; i < table->size; i++)
    {
      assert (table->chains[i] == NULL);
    }
  aig1 = (AIG *) malloc_c32sat (sizeof (AIG));
  aig1->id = 1;
  aig_left_child (aig1) = NULL;
  aig_right_child (aig1) = NULL;
  aig1->hash = 1;
  aig1->refs = 1;
  aig1->next = NULL;
  aig2 = (AIG *) malloc_c32sat (sizeof (AIG));
  aig2->id = 2;
  aig_left_child (aig2) = NULL;
  aig_right_child (aig2) = NULL;
  aig2->hash = 1;
  aig2->refs = 1;
  aig2->next = NULL;
  aig3 = (AIG *) malloc_c32sat (sizeof (AIG));
  aig3->id = 3;
  aig_left_child (aig3) = NULL;
  aig_right_child (aig3) = NULL;
  aig3->hash = 1;
  aig3->refs = 1;
  aig3->next = NULL;
  aig1->next = aig2;
  aig2->next = aig3;
  table->chains[1] = aig1;
  table->num_vars = 3;
  delete_aig_unique_table (table, b_true);
  table = create_aig_unique_table (power);
  aig1 = (AIG *) malloc_c32sat (sizeof (AIG));
  aig1->id = 1;
  aig_left_child (aig1) = NULL;
  aig_right_child (aig1) = NULL;
  aig1->hash = 1;
  aig1->refs = 1;
  aig1->next = NULL;
  table->chains[1] = aig1;
  delete_aig_unique_table (table, b_false);
  assert (is_aig_var (aig1));
  assert (aig1->id == 1);
  assert (aig_right_child (aig1) == NULL);
  assert (aig1->hash == 1);
  assert (aig1->refs == 1);
  assert (aig1->next == NULL);
  free_c32sat (aig1, sizeof (AIG));
  finalise_memory_management ();
}

void
test_var_aig ()
{
  AIGUniqueTable *table = NULL;
  AIG *var1 = NULL;
  AIG *var2 = NULL;
  AIG *var3 = NULL;
  init_error_management (stderr);
  init_memory_management ();
  table = create_aig_unique_table (8);
  var1 = var_aig (&table, 1);
  assert (var1->hash == 1);
  assert (is_aig_var (var1));
  assert (var1->id == 1);
  var2 = var_aig (&table, 2);
  assert (var2->hash == 2);
  assert (is_aig_var (var2));
  assert (var2->id == 2);
  var3 = var_aig (&table, 3);
  assert (var3->hash == 3);
  assert (is_aig_var (var3));
  assert (var3->id == 3);
  var3 = var_aig (&table, 3);
  assert (var3->refs == 2);
  delete_aig_unique_table (table, b_true);
  finalise_memory_management ();
}

void
test_and_aig ()
{
  AIGUniqueTable *table = NULL;
  AIG *left = NULL;
  AIG *right = NULL;
  AIG *and = NULL;
  init_error_management (stderr);
  init_memory_management ();
  table = create_aig_unique_table (8);
  left = var_aig (&table, 1);
  right = var_aig (&table, 2);
  and = and_aig (&table, left, right);
  assert (is_aig_and (and));
  assert (aig_left_child (and) == left);
  assert (aig_right_child (and) == right);
  assert (and == and_aig (&table, left, right));
  assert (and->refs == 2);
  assert (and_aig (&table, AIG_FALSE, AIG_FALSE) == AIG_FALSE);
  assert (and_aig (&table, AIG_FALSE, AIG_TRUE) == AIG_FALSE);
  assert (and_aig (&table, AIG_TRUE, AIG_FALSE) == AIG_FALSE);
  assert (and_aig (&table, AIG_TRUE, AIG_TRUE) == AIG_TRUE);
  delete_aig_unique_table (table, b_true);
  finalise_memory_management ();
}

void
test_invert_aig ()
{
  AIGUniqueTable *table = NULL;
  AIG *left = NULL;
  AIG *right = NULL;
  AIG *and = NULL;
  init_error_management (stderr);
  init_memory_management ();
  table = create_aig_unique_table (8);
  assert (invert_aig (AIG_TRUE) == AIG_FALSE);
  assert (invert_aig (AIG_FALSE) == AIG_TRUE);
  left = var_aig (&table, 23);
  right = var_aig (&table, 24);
  assert (left = invert_aig (invert_aig (left)));
  and = and_aig (&table, left, right);
  assert (and = invert_aig (invert_aig (and)));
  delete_aig_unique_table (table, b_true);
  finalise_memory_management ();
}

void
test_is_aig_constant ()
{
  AIGUniqueTable *table = NULL;
  AIG *x1 = NULL;
  AIG *x2 = NULL;
  AIG *and = NULL;
  init_error_management (stderr);
  init_memory_management ();
  table = create_aig_unique_table (8);
  x1 = var_aig (&table, 1);
  assert (!is_aig_constant (x1));
  x2 = var_aig (&table, 2);
  assert (!is_aig_constant (x2));
  and = and_aig (&table, x1, x2);
  assert (!is_aig_constant (and));
  assert (is_aig_constant (AIG_TRUE));
  assert (is_aig_constant (AIG_FALSE));
  delete_aig_unique_table (table, b_true);
  finalise_memory_management ();
}

void
test_is_inverted_aig ()
{
  AIGUniqueTable *table = NULL;
  AIG *left = NULL;
  AIG *right = NULL;
  AIG *and = NULL;
  init_error_management (stderr);
  init_memory_management ();
  table = create_aig_unique_table (8);
  left = var_aig (&table, 1);
  assert (!is_inverted_aig (left));
  left = invert_aig (left);
  assert (is_inverted_aig (left));
  left = invert_aig (left);
  assert (!is_inverted_aig (left));
  right = var_aig (&table, 2);
  and = and_aig (&table, left, right);
  assert (!is_inverted_aig (and));
  and = invert_aig (and);
  assert (is_inverted_aig (and));
  and = invert_aig (and);
  assert (!is_inverted_aig (and));
  delete_aig_unique_table (table, b_true);
  finalise_memory_management ();
}

void
test_real_address_aig ()
{
  AIGUniqueTable *table = NULL;
  AIG *left = NULL;
  AIG *right = NULL;
  AIG *and = NULL;
  AIG *temp = NULL;
  init_error_management (stderr);
  init_memory_management ();
  table = create_aig_unique_table (8);
  left = var_aig (&table, 1);
  assert (aig_real_address (left) == left);
  temp = invert_aig (left);
  assert (temp != left);
  assert (aig_real_address (temp) == left);
  right = var_aig (&table, 2);
  and = and_aig (&table, left, right);
  assert (aig_real_address (and) == and);
  temp = invert_aig (and);
  assert (temp != and);
  assert (aig_real_address (temp) == and);
  delete_aig_unique_table (table, b_true);
  finalise_memory_management ();
}

void
test_copy_aig ()
{
  AIGUniqueTable *table = NULL;
  AIG *left = NULL;
  AIG *right = NULL;
  AIG *and = NULL;
  init_error_management (stderr);
  init_memory_management ();
  table = create_aig_unique_table (8);
  left = var_aig (&table, 1);
  assert (table->num_vars == 1);
  assert (left->refs == 1);
  right = var_aig (&table, 2);
  assert (table->num_vars == 2);
  assert (right->refs == 1);
  and = and_aig (&table, left, right);
  assert (table->num_ands == 1);
  assert (and->refs == 1);
  left = copy_aig (&table, left);
  assert (table->num_vars == 2);
  assert (left->refs == 3);
  right = copy_aig (&table, right);
  assert (table->num_vars == 2);
  assert (right->refs == 3);
  and = copy_aig (&table, and);
  assert (table->num_ands == 1);
  assert (and->refs == 2);
  and = invert_aig (and);
  and = copy_aig (&table, and);
  and = aig_real_address (and);
  assert (and->refs == 3);
  assert (table->num_vars == 2);
  assert (table->num_ands == 1);
  assert (copy_aig (&table, AIG_TRUE) == AIG_TRUE);
  assert (copy_aig (&table, AIG_FALSE) == AIG_FALSE);
  delete_aig_unique_table (table, b_true);
  finalise_memory_management ();
}

void
test_release_aig ()
{
  AIGUniqueTable *table = NULL;
  AIG *var1 = NULL;
  AIG *var2 = NULL;
  AIG *var3 = NULL;
  AIG *var4 = NULL;
  unsigned int i = 0;
  const int power = 3;
  init_error_management (stderr);
  init_memory_management ();
  table = create_aig_unique_table (power);
  var1 = var_aig (&table, 1);
  var2 = var_aig (&table, 8);
  var3 = var_aig (&table, 16);
  var4 = var_aig (&table, 24);
  assert (var2->next == var3);
  assert (var3->next == var4);
  var3 = copy_aig (&table, var3);
  assert (var3->refs == 2);
  assert (table->num_vars == 4);
  assert (table->num_ands == 0);
  release_aig (&table, var3);
  assert (var3->refs == 1);
  assert (table->num_vars == 4);
  assert (table->num_ands == 0);
  release_aig (&table, var3);
  assert (table->num_vars == 3);
  assert (table->num_ands == 0);
  assert (var2->next == var4);
  release_aig (&table, var2);
  assert (table->num_vars == 2);
  assert (table->num_ands == 0);
  assert (table->chains[0] == var4);
  release_aig (&table, var4);
  assert (table->num_vars == 1);
  assert (table->num_ands == 0);
  release_aig (&table, var1);
  assert (table->num_vars == 0);
  assert (table->num_ands == 0);
  for (i = 0; i < 8; i++)
    {
      assert (table->chains[i] == NULL);
    }
  release_aig (&table, AIG_TRUE);
  release_aig (&table, AIG_FALSE);
  delete_aig_unique_table (table, b_false);
  finalise_memory_management ();
}

void
test_release_aig_recursive ()
{
  AIGUniqueTable *table = NULL;
  AIG *var1 = NULL;
  AIG *var2 = NULL;
  AIG *var3 = NULL;
  AIG *and = NULL;
  AIG *and_top = NULL;
  init_error_management (stderr);
  init_memory_management ();
  table = create_aig_unique_table (8);
  var1 = var_aig (&table, 1);
  var2 = var_aig (&table, 2);
  var3 = var_aig (&table, 3);
  and = and_aig (&table, var1, var2);
  release_aig (&table, var1);
  release_aig (&table, var2);
  and_top = and_aig (&table, var3, and);
  release_aig (&table, var3);
  release_aig (&table, and);
  release_aig (&table, and_top);
  delete_aig_unique_table (table, b_false);
  finalise_memory_management ();
}

void
test_aig_ref_counter_overflow ()
{
  AIG *aig = NULL;
  AIGUniqueTable *table = NULL;
  init_error_management (stderr);
  init_memory_management ();
  table = create_aig_unique_table (8);
  aig = var_aig (&table, 1);
  aig->refs = UINT_MAX;
  copy_aig (&table, aig);
  assert (table->ref_overflow_occured == b_true);
  aig->refs = 1;
  assert (var_aig (&table, 1) == aig);
  release_aig (&table, aig);
  delete_aig_unique_table (table, b_false);
  finalise_memory_management ();
}

void
test_aig_unique_table ()
{
  AIGUniqueTable *table = NULL;
  const int power = 4;
  const int num_vars = 10;
  AIG *vars[num_vars];
  AIG *temp = NULL;
  int i = 0;
  init_error_management (stderr);
  init_memory_management ();
  table = create_aig_unique_table (power);
  for (i = 0; i < num_vars; i++)
    {
      vars[i] = var_aig (&table, i + 1);
      assert (table->num_vars == i + 1);
      assert (table->num_ands == 0);
      assert (vars[i] == var_aig (&table, i + 1));
    }
  temp = var_aig (&table, 20);
  assert (vars[3]->next == temp);
  temp = var_aig (&table, 36);
  assert (vars[3]->next->next == temp);
  assert (temp == var_aig (&table, 36));
  temp = var_aig (&table, 34);
  assert (vars[1]->next == temp);
  temp = var_aig (&table, 1 << power);
  assert (table->chains[0] == temp);
  assert (var_aig (&table, 1 << power) == temp);
  delete_aig_unique_table (table, b_true);
  finalise_memory_management ();
}

void
test_aig_unique_table_enlargement ()
{
  AIGUniqueTable *table = NULL;
  AIG *var1 = NULL;
  AIG *var2 = NULL;
  AIG *var3 = NULL;
  AIG *var4 = NULL;
  AIG *var5 = NULL;
  AIG *and1 = NULL;
  AIG *and2 = NULL;
  AIG *and3 = NULL;
  AIG *and4 = NULL;
  const int power = 0;
  init_error_management (stderr);
  init_memory_management ();
  table = create_aig_unique_table (power);
  var1 = var_aig (&table, 1);
  assert (table->size == 1);
  assert (table->num_vars == 1);
  assert (table->num_ands == 0);
  assert (table->chains[0] == var1);
  assert (var_aig (&table, 1) == var1);
  var2 = var_aig (&table, 2);
  assert (table->size == 2);
  assert (table->num_vars == 2);
  assert (table->num_ands == 0);
  assert (table->chains[0] == var2);
  assert (table->chains[1] == var1);
  assert (var_aig (&table, 1) == var1);
  assert (var_aig (&table, 2) == var2);
  var3 = var_aig (&table, 3);
  assert (table->size == 4);
  assert (table->num_vars == 3);
  assert (table->num_ands == 0);
  assert (table->chains[0] == NULL);
  assert (table->chains[1] == var1);
  assert (table->chains[2] == var2);
  assert (table->chains[3] == var3);
  assert (var_aig (&table, 1) == var1);
  assert (var_aig (&table, 2) == var2);
  assert (var_aig (&table, 3) == var3);
  var4 = var_aig (&table, 7);
  assert (table->size == 4);
  assert (table->num_vars == 4);
  assert (table->num_ands == 0);
  assert (table->chains[0] == NULL);
  assert (table->chains[1] == var1);
  assert (table->chains[2] == var2);
  assert (table->chains[3] == var3);
  assert (table->chains[3]->next == var4);
  assert (var_aig (&table, 1) == var1);
  assert (var_aig (&table, 2) == var2);
  assert (var_aig (&table, 3) == var3);
  assert (var_aig (&table, 7) == var4);
  var5 = var_aig (&table, 5);
  assert (table->size == 8);
  assert (table->num_vars == 5);
  assert (table->num_ands == 0);
  assert (table->chains[0] == NULL);
  assert (table->chains[1] == var1);
  assert (table->chains[2] == var2);
  assert (table->chains[3] == var3);
  assert (table->chains[4] == NULL);
  assert (table->chains[5] == var5);
  assert (table->chains[6] == NULL);
  assert (table->chains[7] == var4);
  assert (var_aig (&table, 1) == var1);
  assert (var_aig (&table, 2) == var2);
  assert (var_aig (&table, 3) == var3);
  assert (var_aig (&table, 7) == var4);
  assert (var_aig (&table, 5) == var5);
  and1 = and_aig (&table, var1, var2);
  assert (table->num_vars == 5);
  assert (table->num_ands == 1);
  and2 = and_aig (&table, var2, var3);
  assert (table->num_vars == 5);
  assert (table->num_ands == 2);
  and3 = and_aig (&table, var1, var3);
  assert (table->num_vars == 5);
  assert (table->num_ands == 3);
  and4 = and_aig (&table, var5, var4);
  assert (table->num_vars == 5);
  assert (table->num_ands == 4);
  assert (table->size == 16);
  assert (var_aig (&table, 1) == var1);
  assert (var_aig (&table, 2) == var2);
  assert (var_aig (&table, 3) == var3);
  assert (var_aig (&table, 7) == var4);
  assert (var_aig (&table, 5) == var5);
  assert (and_aig (&table, var1, var2) == and1);
  assert (and_aig (&table, var2, var3) == and2);
  assert (and_aig (&table, var1, var3) == and3);
  assert (and_aig (&table, var5, var4) == and4);
  delete_aig_unique_table (table, b_true);
  finalise_memory_management ();
}

void
test_aig_unique_table_max_enlargement ()
{
  AIGUniqueTable *table = NULL;
  AIG *left = NULL;
  AIG *right = NULL;
  AIG *and = NULL;
  const int power = AIG_UNIQUE_TABLE_MAX_POWER;
  init_error_management (stderr);
  init_memory_management ();
  table = create_aig_unique_table (power);
  table->size = AIG_UNIQUE_TABLE_MAX_SIZE;
  left = var_aig (&table, 1);
  assert (table->size == AIG_UNIQUE_TABLE_MAX_SIZE);
  right = var_aig (&table, 2);
  assert (table->size == AIG_UNIQUE_TABLE_MAX_SIZE);
  and = and_aig (&table, left, right);
  assert (table->size == AIG_UNIQUE_TABLE_MAX_SIZE);
  release_aig (&table, and);
  release_aig (&table, left);
  release_aig (&table, right);
  table->size = 1 << power;
  delete_aig_unique_table (table, b_false);
  finalise_memory_management ();
}

void
test_aig_unique_table_enlargement_random ()
{
  const unsigned int num_aigs = 1000;
  AIG *vars[num_aigs];
  AIG *ands[num_aigs];
  AIGUniqueTable *table = NULL;
  unsigned int rand_left = 0;
  unsigned int rand_right = 0;
  unsigned int i = 0;
  const int power = 0;
  init_error_management (stderr);
  init_memory_management ();
  table = create_aig_unique_table (power);
  for (i = 0; i < num_aigs; i++)
    {
      vars[i] = var_aig (&table, i + 1);
    }
  for (i = 0; i < num_aigs; i++)
    {
      assert (vars[i] == var_aig (&table, (vars[i])->id));
    }
  for (i = 0; i < num_aigs; i++)
    {
      do
        {
          rand_left = rand () % num_aigs;
          rand_right = rand () % num_aigs;
        }
      while (rand_left == rand_right);
      assert (rand_left != rand_right);
      ands[i] = and_aig (&table, vars[rand_left], vars[rand_right]);
    }
  for (i = 0; i < num_aigs; i++)
    {
      assert (vars[i] == var_aig (&table, (vars[i])->id));
      assert (ands[i] ==
              and_aig (&table, aig_left_child (ands[i]),
                       aig_right_child (ands[i])));
    }
  delete_aig_unique_table (table, b_true);
  finalise_memory_management ();
}


void
test_and_aig_commutative ()
{
  AIGUniqueTable *table = NULL;
  AIG *left = NULL;
  AIG *right = NULL;
  AIG *and = NULL;
  init_error_management (stderr);
  init_memory_management ();
  table = create_aig_unique_table (8);
  left = var_aig (&table, 1);
  right = var_aig (&table, 2);
  and = and_aig (&table, left, right);
  assert (and == and_aig (&table, left, right));
  assert (and == and_aig (&table, right, left));
  left = invert_aig (left);
  assert (and_aig (&table, left, right) != and);
  right = invert_aig (right);
  assert (and_aig (&table, left, right) != and);
  left = invert_aig (left);
  assert (and_aig (&table, left, right) != and);
  delete_aig_unique_table (table, b_true);
  finalise_memory_management ();
}

void
test_aig_simple_optimisations ()
{
  AIGUniqueTable *table = NULL;
  AIG *left = NULL;
  AIG *right = NULL;
  AIG *and = NULL;
  init_error_management (stderr);
  init_memory_management ();
  table = create_aig_unique_table (8);
  assert (and_aig (&table, AIG_FALSE, AIG_FALSE) == AIG_FALSE);
  assert (and_aig (&table, AIG_FALSE, AIG_TRUE) == AIG_FALSE);
  assert (and_aig (&table, AIG_TRUE, AIG_FALSE) == AIG_FALSE);
  assert (and_aig (&table, AIG_TRUE, AIG_TRUE) == AIG_TRUE);
  left = var_aig (&table, 1);
  assert (and_aig (&table, left, AIG_FALSE) == AIG_FALSE);
  assert (and_aig (&table, AIG_FALSE, left) == AIG_FALSE);
  assert (and_aig (&table, left, AIG_TRUE) == left);
  assert (and_aig (&table, AIG_TRUE, left) == left);
  assert (and_aig (&table, left, left) == left);
  assert (and_aig (&table, left, invert_aig (left)) == AIG_FALSE);
  assert (and_aig (&table, invert_aig (left), left) == AIG_FALSE);
  assert (and_aig (&table, invert_aig (left), invert_aig (left)) ==
          invert_aig (left));
  right = var_aig (&table, 2);
  and = and_aig (&table, left, right);
  assert (and_aig (&table, and, AIG_FALSE) == AIG_FALSE);
  assert (and_aig (&table, AIG_FALSE, and) == AIG_FALSE);
  assert (and_aig (&table, and, AIG_TRUE) == and);
  assert (and_aig (&table, AIG_TRUE, and) == and);
  assert (and_aig (&table, and, and) == and);
  assert (and_aig (&table, and, invert_aig (and)) == AIG_FALSE);
  assert (and_aig (&table, invert_aig (and), and) == AIG_FALSE);
  assert (and_aig (&table, invert_aig (and), invert_aig (and)) ==
          invert_aig (and));
  delete_aig_unique_table (table, b_true);
  finalise_memory_management ();
}

void
test_or_aig ()
{
  AIGUniqueTable *table = NULL;
  AIG *left = NULL;
  AIG *right = NULL;
  AIG *or = NULL;
  init_error_management (stderr);
  init_memory_management ();
  table = create_aig_unique_table (8);
  left = var_aig (&table, 1);
  right = var_aig (&table, 2);
  or = or_aig (&table, left, right);
  assert (is_inverted_aig (or));
  or = aig_real_address (or);
  assert (is_aig_and (or));
  assert (is_inverted_aig (aig_left_child (or)));
  assert (is_inverted_aig (aig_right_child (or)));
  assert (aig_real_address (aig_left_child (or)) == left);
  assert (aig_real_address (aig_right_child (or)) == right);
  assert (or_aig (&table, left, AIG_TRUE) == AIG_TRUE);
  assert (or_aig (&table, AIG_TRUE, left) == AIG_TRUE);
  assert (or_aig (&table, AIG_FALSE, left) == left);
  assert (or_aig (&table, left, AIG_FALSE) == left);
  assert (or_aig (&table, left, left) == left);
  assert (or_aig (&table, AIG_FALSE, AIG_FALSE) == AIG_FALSE);
  assert (or_aig (&table, AIG_FALSE, AIG_TRUE) == AIG_TRUE);
  assert (or_aig (&table, AIG_TRUE, AIG_FALSE) == AIG_TRUE);
  assert (or_aig (&table, AIG_TRUE, AIG_TRUE) == AIG_TRUE);
  delete_aig_unique_table (table, b_true);
  finalise_memory_management ();
}

void
test_imp_aig ()
{
  AIGUniqueTable *table = NULL;
  AIG *left = NULL;
  AIG *right = NULL;
  AIG *imp = NULL;
  init_error_management (stderr);
  init_memory_management ();
  table = create_aig_unique_table (8);
  left = var_aig (&table, 1);
  right = var_aig (&table, 2);
  imp = imp_aig (&table, left, right);
  assert (is_inverted_aig (imp));
  imp = aig_real_address (imp);
  assert (is_aig_and (imp));
  assert (!is_inverted_aig (aig_left_child (imp)));
  assert (is_inverted_aig (aig_right_child (imp)));
  assert (aig_left_child (imp) == left);
  assert (aig_real_address (aig_right_child (imp)) == right);
  assert (imp_aig (&table, left, AIG_TRUE) == AIG_TRUE);
  assert (imp_aig (&table, AIG_TRUE, left) == left);
  assert (imp_aig (&table, AIG_FALSE, left) == AIG_TRUE);
  assert (imp_aig (&table, left, AIG_FALSE) == invert_aig (left));
  assert (imp_aig (&table, left, left) == AIG_TRUE);
  assert (imp_aig (&table, AIG_FALSE, AIG_FALSE) == AIG_TRUE);
  assert (imp_aig (&table, AIG_FALSE, AIG_TRUE) == AIG_TRUE);
  assert (imp_aig (&table, AIG_TRUE, AIG_FALSE) == AIG_FALSE);
  assert (imp_aig (&table, AIG_TRUE, AIG_TRUE) == AIG_TRUE);
  delete_aig_unique_table (table, b_true);
  finalise_memory_management ();
}

void
test_dimp_aig ()
{
  AIGUniqueTable *table = NULL;
  AIG *left = NULL;
  AIG *right = NULL;
  AIG *dimp = NULL;
  AIG *dimp_left = NULL;
  AIG *dimp_right = NULL;
  init_error_management (stderr);
  init_memory_management ();
  table = create_aig_unique_table (8);
  left = var_aig (&table, 1);
  right = var_aig (&table, 2);
  dimp = dimp_aig (&table, left, right);
  assert (!is_inverted_aig (dimp));
  assert (is_aig_and (dimp));
  assert (is_inverted_aig (aig_left_child (dimp)));
  assert (is_inverted_aig (aig_right_child (dimp)));
  dimp_left = aig_real_address (aig_left_child (dimp));
  dimp_right = aig_real_address (aig_right_child (dimp));
  assert (!is_inverted_aig (aig_left_child (dimp_left)));
  assert (is_inverted_aig (aig_right_child (dimp_left)));
  assert (aig_left_child (dimp_left) == left);
  assert (aig_real_address (aig_right_child (dimp_left)) == right);
  assert (is_inverted_aig (aig_left_child (dimp_right)));
  assert (!is_inverted_aig (aig_right_child (dimp_right)));
  assert (aig_real_address (aig_left_child (dimp_right)) == left);
  assert (aig_right_child (dimp_right) == right);
  assert (dimp_aig (&table, left, AIG_TRUE) == left);
  assert (dimp_aig (&table, AIG_TRUE, left) == left);
  assert (dimp_aig (&table, AIG_FALSE, left) == invert_aig (left));
  assert (dimp_aig (&table, left, AIG_FALSE) == invert_aig (left));
  assert (dimp_aig (&table, left, left) == AIG_TRUE);
  assert (dimp_aig (&table, AIG_FALSE, AIG_FALSE) == AIG_TRUE);
  assert (dimp_aig (&table, AIG_FALSE, AIG_TRUE) == AIG_FALSE);
  assert (dimp_aig (&table, AIG_TRUE, AIG_FALSE) == AIG_FALSE);
  assert (dimp_aig (&table, AIG_TRUE, AIG_TRUE) == AIG_TRUE);
  delete_aig_unique_table (table, b_true);
  finalise_memory_management ();
}

void
test_xor_aig ()
{
  AIGUniqueTable *table = NULL;
  AIG *left = NULL;
  AIG *right = NULL;
  AIG *xor = NULL;
  AIG *xor_left = NULL;
  AIG *xor_right = NULL;
  init_error_management (stderr);
  init_memory_management ();
  table = create_aig_unique_table (8);
  left = var_aig (&table, 1);
  right = var_aig (&table, 2);
  xor = xor_aig (&table, left, right);
  assert (is_inverted_aig (xor));
  assert (is_aig_and (aig_real_address (xor)));
  assert (is_inverted_aig (aig_left_child (aig_real_address (xor))));
  assert (is_inverted_aig (aig_right_child (aig_real_address (xor))));
  xor_left = aig_real_address (aig_left_child (aig_real_address (xor)));
  xor_right = aig_real_address (aig_right_child (aig_real_address (xor)));
  assert (!is_inverted_aig (aig_left_child (xor_left)));
  assert (is_inverted_aig (aig_right_child (xor_left)));
  assert (aig_left_child (xor_left) == left);
  assert (aig_real_address (aig_right_child (xor_left)) == right);
  assert (is_inverted_aig (aig_left_child (xor_right)));
  assert (!is_inverted_aig (aig_right_child (xor_right)));
  assert (aig_real_address (aig_left_child (xor_right)) == left);
  assert (aig_right_child (xor_right) == right);
  assert (xor_aig (&table, AIG_FALSE, AIG_FALSE) == AIG_FALSE);
  assert (xor_aig (&table, AIG_FALSE, AIG_TRUE) == AIG_TRUE);
  assert (xor_aig (&table, AIG_TRUE, AIG_FALSE) == AIG_TRUE);
  assert (xor_aig (&table, AIG_TRUE, AIG_TRUE) == AIG_FALSE);
  delete_aig_unique_table (table, b_true);
  finalise_memory_management ();
}

void
test_op_aig_releases (AIG * (*f_ptr) (AIGUniqueTable **, AIG *, AIG *))
{
  AIGUniqueTable *table = NULL;
  AIG *var1 = NULL;
  AIG *var2 = NULL;
  AIG *result = NULL;
  init_error_management (stderr);
  init_memory_management ();
  table = create_aig_unique_table (8);
  var1 = var_aig (&table, 1);
  var2 = var_aig (&table, 2);
  result = f_ptr (&table, var1, var2);
  release_aig (&table, result);
  release_aig (&table, var1);
  release_aig (&table, var2);
  delete_aig_unique_table (table, b_false);
  finalise_memory_management ();
}

void
test_and_aig_releases ()
{
  test_op_aig_releases (and_aig);
}

void
test_or_aig_releases ()
{
  test_op_aig_releases (or_aig);
}

void
test_imp_aig_releases ()
{
  test_op_aig_releases (imp_aig);
}

void
test_dimp_aig_releases ()
{
  test_op_aig_releases (dimp_aig);
}

void
test_xor_aig_releases ()
{
  test_op_aig_releases (xor_aig);
}

void
test_op_aig_array3 (AIG
                    * (*f_ptr) (AIGUniqueTable **, AIG **, int),
                    const AIG * expected_results[8])
{
  AIGUniqueTable *table;
  int pos = 0;
  AIG *aigs[3];
  init_error_management (stderr);
  init_memory_management ();
  table = create_aig_unique_table (8);
  aigs[0] = AIG_FALSE;
  aigs[1] = AIG_FALSE;
  aigs[2] = AIG_FALSE;
  assert (f_ptr (&table, aigs, 3) == expected_results[pos++]);
  aigs[0] = AIG_FALSE;
  aigs[1] = AIG_FALSE;
  aigs[2] = AIG_TRUE;
  assert (f_ptr (&table, aigs, 3) == expected_results[pos++]);
  aigs[0] = AIG_FALSE;
  aigs[1] = AIG_TRUE;
  aigs[2] = AIG_FALSE;
  assert (f_ptr (&table, aigs, 3) == expected_results[pos++]);
  aigs[0] = AIG_FALSE;
  aigs[1] = AIG_TRUE;
  aigs[2] = AIG_TRUE;
  assert (f_ptr (&table, aigs, 3) == expected_results[pos++]);
  aigs[0] = AIG_TRUE;
  aigs[1] = AIG_FALSE;
  aigs[2] = AIG_FALSE;
  assert (f_ptr (&table, aigs, 3) == expected_results[pos++]);
  aigs[0] = AIG_TRUE;
  aigs[1] = AIG_FALSE;
  aigs[2] = AIG_TRUE;
  assert (f_ptr (&table, aigs, 3) == expected_results[pos++]);
  aigs[0] = AIG_TRUE;
  aigs[1] = AIG_TRUE;
  aigs[2] = AIG_FALSE;
  assert (f_ptr (&table, aigs, 3) == expected_results[pos++]);
  aigs[0] = AIG_TRUE;
  aigs[1] = AIG_TRUE;
  aigs[2] = AIG_TRUE;
  assert (f_ptr (&table, aigs, 3) == expected_results[pos++]);
  delete_aig_unique_table (table, b_false);
  finalise_memory_management ();
}

void
test_op_aig_array4 (AIG
                    * (*f_ptr) (AIGUniqueTable **, AIG **, int),
                    const AIG * expected_results[16])
{
  AIGUniqueTable *table;
  int pos = 0;
  AIG *aigs[4];
  init_error_management (stderr);
  init_memory_management ();
  table = create_aig_unique_table (8);
  aigs[0] = AIG_FALSE;
  aigs[1] = AIG_FALSE;
  aigs[2] = AIG_FALSE;
  aigs[3] = AIG_FALSE;
  assert (f_ptr (&table, aigs, 4) == expected_results[pos++]);
  aigs[0] = AIG_FALSE;
  aigs[1] = AIG_FALSE;
  aigs[2] = AIG_FALSE;
  aigs[3] = AIG_TRUE;
  assert (f_ptr (&table, aigs, 4) == expected_results[pos++]);
  aigs[0] = AIG_FALSE;
  aigs[1] = AIG_FALSE;
  aigs[2] = AIG_TRUE;
  aigs[3] = AIG_FALSE;
  assert (f_ptr (&table, aigs, 4) == expected_results[pos++]);
  aigs[0] = AIG_FALSE;
  aigs[1] = AIG_FALSE;
  aigs[2] = AIG_TRUE;
  aigs[3] = AIG_TRUE;
  assert (f_ptr (&table, aigs, 4) == expected_results[pos++]);
  aigs[0] = AIG_FALSE;
  aigs[1] = AIG_TRUE;
  aigs[2] = AIG_FALSE;
  aigs[3] = AIG_FALSE;
  assert (f_ptr (&table, aigs, 4) == expected_results[pos++]);
  aigs[0] = AIG_FALSE;
  aigs[1] = AIG_TRUE;
  aigs[2] = AIG_FALSE;
  aigs[3] = AIG_TRUE;
  assert (f_ptr (&table, aigs, 4) == expected_results[pos++]);
  aigs[0] = AIG_FALSE;
  aigs[1] = AIG_TRUE;
  aigs[2] = AIG_TRUE;
  aigs[3] = AIG_FALSE;
  assert (f_ptr (&table, aigs, 4) == expected_results[pos++]);
  aigs[0] = AIG_FALSE;
  aigs[1] = AIG_TRUE;
  aigs[2] = AIG_TRUE;
  aigs[3] = AIG_TRUE;
  assert (f_ptr (&table, aigs, 4) == expected_results[pos++]);
  aigs[0] = AIG_TRUE;
  aigs[1] = AIG_FALSE;
  aigs[2] = AIG_FALSE;
  aigs[3] = AIG_FALSE;
  assert (f_ptr (&table, aigs, 4) == expected_results[pos++]);
  aigs[0] = AIG_TRUE;
  aigs[1] = AIG_FALSE;
  aigs[2] = AIG_FALSE;
  aigs[3] = AIG_TRUE;
  assert (f_ptr (&table, aigs, 4) == expected_results[pos++]);
  aigs[0] = AIG_TRUE;
  aigs[1] = AIG_FALSE;
  aigs[2] = AIG_TRUE;
  aigs[3] = AIG_FALSE;
  assert (f_ptr (&table, aigs, 4) == expected_results[pos++]);
  aigs[0] = AIG_TRUE;
  aigs[1] = AIG_FALSE;
  aigs[2] = AIG_TRUE;
  aigs[3] = AIG_TRUE;
  assert (f_ptr (&table, aigs, 4) == expected_results[pos++]);
  aigs[0] = AIG_TRUE;
  aigs[1] = AIG_TRUE;
  aigs[2] = AIG_FALSE;
  aigs[3] = AIG_FALSE;
  assert (f_ptr (&table, aigs, 4) == expected_results[pos++]);
  aigs[0] = AIG_TRUE;
  aigs[1] = AIG_TRUE;
  aigs[2] = AIG_FALSE;
  aigs[3] = AIG_TRUE;
  assert (f_ptr (&table, aigs, 4) == expected_results[pos++]);
  aigs[0] = AIG_TRUE;
  aigs[1] = AIG_TRUE;
  aigs[2] = AIG_TRUE;
  aigs[3] = AIG_FALSE;
  assert (f_ptr (&table, aigs, 4) == expected_results[pos++]);
  aigs[0] = AIG_TRUE;
  aigs[1] = AIG_TRUE;
  aigs[2] = AIG_TRUE;
  aigs[3] = AIG_TRUE;
  assert (f_ptr (&table, aigs, 4) == expected_results[pos++]);
  delete_aig_unique_table (table, b_false);
  finalise_memory_management ();
}

void
test_and_aig_array ()
{
  test_op_aig_array3 (and_aig_array, g_and_aig_3_expected_results);
  test_op_aig_array4 (and_aig_array, g_and_aig_4_expected_results);
}

void
test_or_aig_array ()
{
  test_op_aig_array3 (or_aig_array, g_or_aig_3_expected_results);
  test_op_aig_array4 (or_aig_array, g_or_aig_4_expected_results);
}

void
test_dimp_aig_array ()
{
  test_op_aig_array3 (dimp_aig_array, g_dimp_aig_3_expected_results);
  test_op_aig_array4 (dimp_aig_array, g_dimp_aig_4_expected_results);
}

void
test_xor_aig_array ()
{
  test_op_aig_array3 (xor_aig_array, g_xor_aig_3_expected_results);
  test_op_aig_array4 (xor_aig_array, g_xor_aig_4_expected_results);
}

void
test_op_aig_array_releases (AIG * (*f_ptr) (AIGUniqueTable **, AIG **, int))
{
  AIGUniqueTable *table = NULL;
  AIG *result = NULL;
  const int aigs_size = 5;
  AIG *aigs[aigs_size];
  int i = 0;
  init_error_management (stderr);
  init_memory_management ();
  table = create_aig_unique_table (8);
  for (i = 0; i < aigs_size; i++)
    {
      aigs[i] = var_aig (&table, i + 1);
    }
  result = f_ptr (&table, aigs, aigs_size);
  release_aig (&table, result);
  for (i = 0; i < aigs_size; i++)
    {
      release_aig (&table, aigs[i]);
    }
  delete_aig_unique_table (table, b_false);
  finalise_memory_management ();
}

void
test_and_aig_array_releases ()
{
  test_op_aig_array_releases (and_aig_array);
}

void
test_or_aig_array_releases ()
{
  test_op_aig_array_releases (or_aig_array);
}

void
test_dimp_aig_array_releases ()
{
  test_op_aig_array_releases (dimp_aig_array);
}

void
test_xor_aig_array_releases ()
{
  test_op_aig_array_releases (xor_aig_array);
}

void
test_op_aig_va_list3 (AIG
                      * (*f_ptr) (AIGUniqueTable **, int, ...),
                      const AIG * expected_results[8])
{
  AIGUniqueTable *table;
  int pos = 0;
  init_error_management (stderr);
  init_memory_management ();
  table = create_aig_unique_table (8);
  assert (f_ptr (&table, 3, AIG_FALSE, AIG_FALSE, AIG_FALSE) ==
          expected_results[pos++]);
  assert (f_ptr (&table, 3, AIG_FALSE, AIG_FALSE, AIG_TRUE) ==
          expected_results[pos++]);
  assert (f_ptr (&table, 3, AIG_FALSE, AIG_TRUE, AIG_FALSE) ==
          expected_results[pos++]);
  assert (f_ptr (&table, 3, AIG_FALSE, AIG_TRUE, AIG_TRUE) ==
          expected_results[pos++]);
  assert (f_ptr (&table, 3, AIG_TRUE, AIG_FALSE, AIG_FALSE) ==
          expected_results[pos++]);
  assert (f_ptr (&table, 3, AIG_TRUE, AIG_FALSE, AIG_TRUE) ==
          expected_results[pos++]);
  assert (f_ptr (&table, 3, AIG_TRUE, AIG_TRUE, AIG_FALSE) ==
          expected_results[pos++]);
  assert (f_ptr (&table, 3, AIG_TRUE, AIG_TRUE, AIG_TRUE) ==
          expected_results[pos++]);
  delete_aig_unique_table (table, b_false);
  finalise_memory_management ();
}

void
test_op_aig_va_list4 (AIG
                      * (*f_ptr) (AIGUniqueTable **, int, ...),
                      const AIG * expected_results[16])
{
  AIGUniqueTable *table;
  int pos = 0;
  init_error_management (stderr);
  init_memory_management ();
  table = create_aig_unique_table (8);
  assert (f_ptr (&table, 4, AIG_FALSE, AIG_FALSE, AIG_FALSE, AIG_FALSE) ==
          expected_results[pos++]);
  assert (f_ptr (&table, 4, AIG_FALSE, AIG_FALSE, AIG_FALSE, AIG_TRUE) ==
          expected_results[pos++]);
  assert (f_ptr (&table, 4, AIG_FALSE, AIG_FALSE, AIG_TRUE, AIG_FALSE) ==
          expected_results[pos++]);
  assert (f_ptr (&table, 4, AIG_FALSE, AIG_FALSE, AIG_TRUE, AIG_TRUE) ==
          expected_results[pos++]);
  assert (f_ptr (&table, 4, AIG_FALSE, AIG_TRUE, AIG_FALSE, AIG_FALSE) ==
          expected_results[pos++]);
  assert (f_ptr (&table, 4, AIG_FALSE, AIG_TRUE, AIG_FALSE, AIG_TRUE) ==
          expected_results[pos++]);
  assert (f_ptr (&table, 4, AIG_FALSE, AIG_TRUE, AIG_TRUE, AIG_FALSE) ==
          expected_results[pos++]);
  assert (f_ptr (&table, 4, AIG_FALSE, AIG_TRUE, AIG_TRUE, AIG_TRUE) ==
          expected_results[pos++]);
  assert (f_ptr (&table, 4, AIG_TRUE, AIG_FALSE, AIG_FALSE, AIG_FALSE) ==
          expected_results[pos++]);
  assert (f_ptr (&table, 4, AIG_TRUE, AIG_FALSE, AIG_FALSE, AIG_TRUE) ==
          expected_results[pos++]);
  assert (f_ptr (&table, 4, AIG_TRUE, AIG_FALSE, AIG_TRUE, AIG_FALSE) ==
          expected_results[pos++]);
  assert (f_ptr (&table, 4, AIG_TRUE, AIG_FALSE, AIG_TRUE, AIG_TRUE) ==
          expected_results[pos++]);
  assert (f_ptr (&table, 4, AIG_TRUE, AIG_TRUE, AIG_FALSE, AIG_FALSE) ==
          expected_results[pos++]);
  assert (f_ptr (&table, 4, AIG_TRUE, AIG_TRUE, AIG_FALSE, AIG_TRUE) ==
          expected_results[pos++]);
  assert (f_ptr (&table, 4, AIG_TRUE, AIG_TRUE, AIG_TRUE, AIG_FALSE) ==
          expected_results[pos++]);
  assert (f_ptr (&table, 4, AIG_TRUE, AIG_TRUE, AIG_TRUE, AIG_TRUE) ==
          expected_results[pos++]);
  delete_aig_unique_table (table, b_false);
  finalise_memory_management ();
}

void
test_and_aig_va_list ()
{
  test_op_aig_va_list3 (and_aig_va_list, g_and_aig_3_expected_results);
  test_op_aig_va_list4 (and_aig_va_list, g_and_aig_4_expected_results);
}

void
test_or_aig_va_list ()
{
  test_op_aig_va_list3 (or_aig_va_list, g_or_aig_3_expected_results);
  test_op_aig_va_list4 (or_aig_va_list, g_or_aig_4_expected_results);
}

void
test_dimp_aig_va_list ()
{
  test_op_aig_va_list3 (dimp_aig_va_list, g_dimp_aig_3_expected_results);
  test_op_aig_va_list4 (dimp_aig_va_list, g_dimp_aig_4_expected_results);
}

void
test_xor_aig_va_list ()
{
  test_op_aig_va_list3 (xor_aig_va_list, g_xor_aig_3_expected_results);
  test_op_aig_va_list4 (xor_aig_va_list, g_xor_aig_4_expected_results);
}

void
test_op_aig_va_list_releases (AIG * (*f_ptr) (AIGUniqueTable **, int, ...))
{
  AIGUniqueTable *table = NULL;
  AIG *result = NULL;
  AIG *var1 = NULL;
  AIG *var2 = NULL;
  AIG *var3 = NULL;
  AIG *var4 = NULL;
  AIG *var5 = NULL;
  init_error_management (stderr);
  init_memory_management ();
  table = create_aig_unique_table (8);
  var1 = var_aig (&table, 1);
  var2 = var_aig (&table, 2);
  var3 = var_aig (&table, 3);
  var4 = var_aig (&table, 4);
  var5 = var_aig (&table, 5);
  result = f_ptr (&table, 5, var1, var2, var3, var4, var5);
  release_aig (&table, result);
  release_aig (&table, var1);
  release_aig (&table, var2);
  release_aig (&table, var3);
  release_aig (&table, var4);
  release_aig (&table, var5);
  delete_aig_unique_table (table, b_false);
  finalise_memory_management ();
}

void
test_and_aig_va_list_releases ()
{
  test_op_aig_va_list_releases (and_aig_va_list);
}

void
test_or_aig_va_list_releases ()
{
  test_op_aig_va_list_releases (or_aig_va_list);
}

void
test_dimp_aig_va_list_releases ()
{
  test_op_aig_va_list_releases (dimp_aig_va_list);
}

void
test_xor_aig_va_list_releases ()
{
  test_op_aig_va_list_releases (xor_aig_va_list);
}

void
test_full_add_aig (AIG * x, AIG * y, AIG * cin,
                   AIG * result_expected, AIG * cout_expected)
{
  AIGUniqueTable *table = NULL;
  AIG *result = NULL;
  AIG *cout = NULL;
  init_error_management (stderr);
  init_memory_management ();
  table = create_aig_unique_table (8);
  result = full_add_aig (&table, x, y, cin, &cout);
  assert (result == result_expected);
  assert (cout == cout_expected);
  delete_aig_unique_table (table, b_true);
  finalise_memory_management ();
}

void
test_full_add_aig_1 ()
{
  test_full_add_aig (AIG_FALSE, AIG_FALSE, AIG_FALSE, AIG_FALSE, AIG_FALSE);
}

void
test_full_add_aig_2 ()
{
  test_full_add_aig (AIG_FALSE, AIG_FALSE, AIG_TRUE, AIG_TRUE, AIG_FALSE);
}

void
test_full_add_aig_3 ()
{
  test_full_add_aig (AIG_FALSE, AIG_TRUE, AIG_FALSE, AIG_TRUE, AIG_FALSE);
}

void
test_full_add_aig_4 ()
{
  test_full_add_aig (AIG_FALSE, AIG_TRUE, AIG_TRUE, AIG_FALSE, AIG_TRUE);
}

void
test_full_add_aig_5 ()
{
  test_full_add_aig (AIG_TRUE, AIG_FALSE, AIG_FALSE, AIG_TRUE, AIG_FALSE);
}

void
test_full_add_aig_6 ()
{
  test_full_add_aig (AIG_TRUE, AIG_FALSE, AIG_TRUE, AIG_FALSE, AIG_TRUE);
}

void
test_full_add_aig_7 ()
{
  test_full_add_aig (AIG_TRUE, AIG_TRUE, AIG_FALSE, AIG_FALSE, AIG_TRUE);
}

void
test_full_add_aig_8 ()
{
  test_full_add_aig (AIG_TRUE, AIG_TRUE, AIG_TRUE, AIG_TRUE, AIG_TRUE);
}

void
test_full_add_aig_releases ()
{
  AIGUniqueTable *table = NULL;
  AIG *x = NULL;
  AIG *y = NULL;
  AIG *cin = NULL;
  AIG *result = NULL;
  AIG *cout = NULL;
  init_error_management (stderr);
  init_memory_management ();
  table = create_aig_unique_table (8);
  x = var_aig (&table, 1);
  y = var_aig (&table, 2);
  cin = var_aig (&table, 3);
  result = full_add_aig (&table, x, y, cin, &cout);
  release_aig (&table, x);
  release_aig (&table, y);
  release_aig (&table, cin);
  release_aig (&table, result);
  release_aig (&table, cout);
  assert (table->num_vars == 0);
  assert (table->num_ands == 0);
  delete_aig_unique_table (table, b_false);
  finalise_memory_management ();
}

void
test_ripple_compare_aig (AIG * x, AIG * y, AIG * lt_in,
                         AIG * eq_in, AIG * gt_in,
                         AIG * lt_out_expected,
                         AIG * eq_out_expected, AIG * gt_out_expected)
{
  AIGUniqueTable *table = NULL;
  AIG *lt_out = NULL;
  AIG *eq_out = NULL;
  AIG *gt_out = NULL;
  init_error_management (stderr);
  init_memory_management ();
  table = create_aig_unique_table (8);
  ripple_compare_aig (&table, x, y, lt_in, eq_in, gt_in, &lt_out, &eq_out,
                      &gt_out);
  assert (lt_out == lt_out_expected);
  assert (eq_out == eq_out_expected);
  assert (gt_out == gt_out_expected);
  delete_aig_unique_table (table, b_true);
  finalise_memory_management ();
}

void
test_ripple_compare_aig_1 ()
{
  test_ripple_compare_aig (AIG_FALSE, AIG_FALSE, AIG_FALSE, AIG_FALSE,
                           AIG_FALSE, AIG_FALSE, AIG_FALSE, AIG_FALSE);
}

void
test_ripple_compare_aig_2 ()
{
  test_ripple_compare_aig (AIG_FALSE, AIG_FALSE, AIG_FALSE, AIG_FALSE,
                           AIG_TRUE, AIG_FALSE, AIG_FALSE, AIG_TRUE);
}

void
test_ripple_compare_aig_3 ()
{
  test_ripple_compare_aig (AIG_FALSE, AIG_FALSE, AIG_FALSE, AIG_TRUE,
                           AIG_FALSE, AIG_FALSE, AIG_TRUE, AIG_FALSE);
}

void
test_ripple_compare_aig_4 ()
{
  test_ripple_compare_aig (AIG_FALSE, AIG_FALSE, AIG_FALSE, AIG_TRUE,
                           AIG_TRUE, AIG_FALSE, AIG_FALSE, AIG_FALSE);
}

void
test_ripple_compare_aig_5 ()
{
  test_ripple_compare_aig (AIG_FALSE, AIG_FALSE, AIG_TRUE, AIG_FALSE,
                           AIG_FALSE, AIG_TRUE, AIG_FALSE, AIG_FALSE);
}

void
test_ripple_compare_aig_6 ()
{
  test_ripple_compare_aig (AIG_FALSE, AIG_FALSE, AIG_TRUE, AIG_FALSE,
                           AIG_TRUE, AIG_FALSE, AIG_FALSE, AIG_FALSE);
}

void
test_ripple_compare_aig_7 ()
{
  test_ripple_compare_aig (AIG_FALSE, AIG_FALSE, AIG_TRUE, AIG_TRUE,
                           AIG_FALSE, AIG_FALSE, AIG_FALSE, AIG_FALSE);
}

void
test_ripple_compare_aig_8 ()
{
  test_ripple_compare_aig (AIG_FALSE, AIG_FALSE, AIG_TRUE, AIG_TRUE, AIG_TRUE,
                           AIG_FALSE, AIG_FALSE, AIG_FALSE);
}

void
test_ripple_compare_aig_9 ()
{
  test_ripple_compare_aig (AIG_FALSE, AIG_TRUE, AIG_FALSE, AIG_FALSE,
                           AIG_FALSE, AIG_FALSE, AIG_FALSE, AIG_FALSE);
}

void
test_ripple_compare_aig_10 ()
{
  test_ripple_compare_aig (AIG_FALSE, AIG_TRUE, AIG_FALSE, AIG_FALSE,
                           AIG_TRUE, AIG_FALSE, AIG_FALSE, AIG_TRUE);
}

void
test_ripple_compare_aig_11 ()
{
  test_ripple_compare_aig (AIG_FALSE, AIG_TRUE, AIG_FALSE, AIG_TRUE,
                           AIG_FALSE, AIG_TRUE, AIG_FALSE, AIG_FALSE);
}

void
test_ripple_compare_aig_12 ()
{
  test_ripple_compare_aig (AIG_FALSE, AIG_TRUE, AIG_FALSE, AIG_TRUE, AIG_TRUE,
                           AIG_FALSE, AIG_FALSE, AIG_FALSE);
}

void
test_ripple_compare_aig_13 ()
{
  test_ripple_compare_aig (AIG_FALSE, AIG_TRUE, AIG_TRUE, AIG_FALSE,
                           AIG_FALSE, AIG_TRUE, AIG_FALSE, AIG_FALSE);
}

void
test_ripple_compare_aig_14 ()
{
  test_ripple_compare_aig (AIG_FALSE, AIG_TRUE, AIG_TRUE, AIG_FALSE, AIG_TRUE,
                           AIG_FALSE, AIG_FALSE, AIG_FALSE);
}

void
test_ripple_compare_aig_15 ()
{
  test_ripple_compare_aig (AIG_FALSE, AIG_TRUE, AIG_TRUE, AIG_TRUE, AIG_FALSE,
                           AIG_FALSE, AIG_FALSE, AIG_FALSE);
}

void
test_ripple_compare_aig_16 ()
{
  test_ripple_compare_aig (AIG_FALSE, AIG_TRUE, AIG_TRUE, AIG_TRUE, AIG_TRUE,
                           AIG_FALSE, AIG_FALSE, AIG_FALSE);
}

void
test_ripple_compare_aig_17 ()
{
  test_ripple_compare_aig (AIG_TRUE, AIG_FALSE, AIG_FALSE, AIG_FALSE,
                           AIG_FALSE, AIG_FALSE, AIG_FALSE, AIG_FALSE);
}

void
test_ripple_compare_aig_18 ()
{
  test_ripple_compare_aig (AIG_TRUE, AIG_FALSE, AIG_FALSE, AIG_FALSE,
                           AIG_TRUE, AIG_FALSE, AIG_FALSE, AIG_TRUE);
}

void
test_ripple_compare_aig_19 ()
{
  test_ripple_compare_aig (AIG_TRUE, AIG_FALSE, AIG_FALSE, AIG_TRUE,
                           AIG_FALSE, AIG_FALSE, AIG_FALSE, AIG_TRUE);
}

void
test_ripple_compare_aig_20 ()
{
  test_ripple_compare_aig (AIG_TRUE, AIG_FALSE, AIG_FALSE, AIG_TRUE, AIG_TRUE,
                           AIG_FALSE, AIG_FALSE, AIG_FALSE);
}

void
test_ripple_compare_aig_21 ()
{
  test_ripple_compare_aig (AIG_TRUE, AIG_FALSE, AIG_TRUE, AIG_FALSE,
                           AIG_FALSE, AIG_TRUE, AIG_FALSE, AIG_FALSE);
}

void
test_ripple_compare_aig_22 ()
{
  test_ripple_compare_aig (AIG_TRUE, AIG_FALSE, AIG_TRUE, AIG_FALSE, AIG_TRUE,
                           AIG_FALSE, AIG_FALSE, AIG_FALSE);
}

void
test_ripple_compare_aig_23 ()
{
  test_ripple_compare_aig (AIG_TRUE, AIG_FALSE, AIG_TRUE, AIG_TRUE, AIG_FALSE,
                           AIG_FALSE, AIG_FALSE, AIG_FALSE);
}

void
test_ripple_compare_aig_24 ()
{
  test_ripple_compare_aig (AIG_TRUE, AIG_FALSE, AIG_TRUE, AIG_TRUE, AIG_TRUE,
                           AIG_FALSE, AIG_FALSE, AIG_FALSE);
}

void
test_ripple_compare_aig_25 ()
{
  test_ripple_compare_aig (AIG_TRUE, AIG_TRUE, AIG_FALSE, AIG_FALSE,
                           AIG_FALSE, AIG_FALSE, AIG_FALSE, AIG_FALSE);
}

void
test_ripple_compare_aig_26 ()
{
  test_ripple_compare_aig (AIG_TRUE, AIG_TRUE, AIG_FALSE, AIG_FALSE, AIG_TRUE,
                           AIG_FALSE, AIG_FALSE, AIG_TRUE);
}

void
test_ripple_compare_aig_27 ()
{
  test_ripple_compare_aig (AIG_TRUE, AIG_TRUE, AIG_FALSE, AIG_TRUE, AIG_FALSE,
                           AIG_FALSE, AIG_TRUE, AIG_FALSE);
}

void
test_ripple_compare_aig_28 ()
{
  test_ripple_compare_aig (AIG_TRUE, AIG_TRUE, AIG_FALSE, AIG_TRUE, AIG_TRUE,
                           AIG_FALSE, AIG_FALSE, AIG_FALSE);
}

void
test_ripple_compare_aig_29 ()
{
  test_ripple_compare_aig (AIG_TRUE, AIG_TRUE, AIG_TRUE, AIG_FALSE, AIG_FALSE,
                           AIG_TRUE, AIG_FALSE, AIG_FALSE);
}

void
test_ripple_compare_aig_30 ()
{
  test_ripple_compare_aig (AIG_TRUE, AIG_TRUE, AIG_TRUE, AIG_FALSE, AIG_TRUE,
                           AIG_FALSE, AIG_FALSE, AIG_FALSE);
}

void
test_ripple_compare_aig_31 ()
{
  test_ripple_compare_aig (AIG_TRUE, AIG_TRUE, AIG_TRUE, AIG_TRUE, AIG_FALSE,
                           AIG_FALSE, AIG_FALSE, AIG_FALSE);
}

void
test_ripple_compare_aig_32 ()
{
  test_ripple_compare_aig (AIG_TRUE, AIG_TRUE, AIG_TRUE, AIG_TRUE, AIG_TRUE,
                           AIG_FALSE, AIG_FALSE, AIG_FALSE);
}

void
test_ripple_compare_aig_releases ()
{
  AIGUniqueTable *table = NULL;
  AIG *x = NULL;
  AIG *y = NULL;
  AIG *lt_in = NULL;
  AIG *eq_in = NULL;
  AIG *gt_in = NULL;
  AIG *lt_out = NULL;
  AIG *eq_out = NULL;
  AIG *gt_out = NULL;
  init_error_management (stderr);
  init_memory_management ();
  table = create_aig_unique_table (8);
  x = var_aig (&table, 1);
  y = var_aig (&table, 2);
  lt_in = var_aig (&table, 3);
  eq_in = var_aig (&table, 4);
  gt_in = var_aig (&table, 5);
  ripple_compare_aig (&table, x, y, lt_in, eq_in, gt_in, &lt_out, &eq_out,
                      &gt_out);
  release_aig (&table, x);
  release_aig (&table, y);
  release_aig (&table, lt_in);
  release_aig (&table, eq_in);
  release_aig (&table, gt_in);
  release_aig (&table, lt_out);
  release_aig (&table, eq_out);
  release_aig (&table, gt_out);
  assert (table->num_vars == 0);
  assert (table->num_ands == 0);
  delete_aig_unique_table (table, b_false);
  finalise_memory_management ();
}

void
test_too_many_aigs_error_var ()
{
  FILE *err_output =
    fopen ("output/aig_too_many_aigs_error_var_output.txt", "w");
  AIGUniqueTable *table = NULL;
  AIG *aig1 = NULL;
  AIG *aig2 = NULL;
  AIG *aig3 = NULL;
  AIG *aig4 = NULL;
  AIG *and1 = NULL;
  AIG *and2 = NULL;
  AIG *and3 = NULL;
  ext_number_of_supported_aigs = 3;
  init_error_management (err_output);
  init_memory_management ();
  assert (!ext_too_many_aigs_error_occured);
  table = create_aig_unique_table (8);
  aig1 = var_aig (&table, 1);
  assert (!ext_too_many_aigs_error_occured);
  aig2 = var_aig (&table, 2);
  assert (!ext_too_many_aigs_error_occured);
  and1 = and_aig (&table, aig1, aig2);
  assert (!ext_too_many_aigs_error_occured);
  aig3 = var_aig (&table, 3);
  assert (aig3 == AIG_FALSE);
  assert (ext_too_many_aigs_error_occured);
  and2 = and_aig (&table, and1, invert_aig (aig1));
  assert (and2 == AIG_FALSE);
  aig4 = var_aig (&table, 1);
  assert (is_aig_var (aig4));
  and3 = and_aig (&table, aig1, aig2);
  assert (is_aig_and (and3));
  release_aig (&table, aig1);
  release_aig (&table, aig2);
  release_aig (&table, aig3);
  release_aig (&table, aig4);
  release_aig (&table, and1);
  release_aig (&table, and2);
  release_aig (&table, and3);
  delete_aig_unique_table (table, b_false);
  finalise_memory_management ();
  fclose (err_output);
  ext_number_of_supported_aigs = CONFIG_DEFAULT_NUMBER_OF_SUPPORTED_AIGS;
}

void
test_too_many_aigs_error_and ()
{
  FILE *err_output =
    fopen ("output/aig_too_many_aigs_error_and_output.txt", "w");
  AIGUniqueTable *table = NULL;
  AIG *aig1 = NULL;
  AIG *aig2 = NULL;
  AIG *aig3 = NULL;
  AIG *aig4 = NULL;
  AIG *aig5 = NULL;
  AIG *and1 = NULL;
  AIG *and2 = NULL;
  AIG *and3 = NULL;
  ext_number_of_supported_aigs = 4;
  init_error_management (err_output);
  init_memory_management ();
  assert (!ext_too_many_aigs_error_occured);
  table = create_aig_unique_table (8);
  aig1 = var_aig (&table, 1);
  assert (!ext_too_many_aigs_error_occured);
  aig2 = var_aig (&table, 2);
  assert (!ext_too_many_aigs_error_occured);
  aig3 = var_aig (&table, 3);
  assert (!ext_too_many_aigs_error_occured);
  and1 = and_aig (&table, aig1, aig2);
  assert (!ext_too_many_aigs_error_occured);
  and2 = and_aig (&table, and1, aig3);
  assert (ext_too_many_aigs_error_occured);
  assert (and2 == AIG_FALSE);
  aig4 = var_aig (&table, 10);
  assert (aig4 == AIG_FALSE);
  and3 = and_aig (&table, aig1, aig2);
  assert (is_aig_and (and3));
  aig5 = var_aig (&table, 1);
  assert (is_aig_var (aig5));
  release_aig (&table, aig1);
  release_aig (&table, aig2);
  release_aig (&table, aig3);
  release_aig (&table, aig4);
  release_aig (&table, aig5);
  release_aig (&table, and1);
  release_aig (&table, and2);
  release_aig (&table, and3);
  delete_aig_unique_table (table, b_false);
  finalise_memory_management ();
  fclose (err_output);
  ext_number_of_supported_aigs = CONFIG_DEFAULT_NUMBER_OF_SUPPORTED_AIGS;
}

void
test_print_aig_constant_true ()
{
  FILE *output = fopen ("output/aig_print_constant_true_output.txt", "w");
  AIGUniqueTable *table = NULL;
  AIG *aig = AIG_TRUE;
  init_error_management (stderr);
  init_memory_management ();
  init_aig_id_generation (1);
  table = create_aig_unique_table (8);
  print_aig (aig, table, output);
  delete_aig_unique_table (table, b_false);
  finalise_memory_management ();
  fclose (output);
}

void
test_print_aig_constant_false ()
{
  FILE *output = fopen ("output/aig_print_constant_false_output.txt", "w");
  AIGUniqueTable *table = NULL;
  AIG *aig = AIG_FALSE;
  init_error_management (stderr);
  init_memory_management ();
  init_aig_id_generation (1);
  table = create_aig_unique_table (8);
  print_aig (aig, table, output);
  delete_aig_unique_table (table, b_false);
  finalise_memory_management ();
  fclose (output);
}

void
test_print_aig_var ()
{
  FILE *output = fopen ("output/aig_print_var_output.txt", "w");
  AIGUniqueTable *table = NULL;
  AIG *var = NULL;
  init_error_management (stderr);
  init_memory_management ();
  init_aig_id_generation (1);
  table = create_aig_unique_table (8);
  var = var_aig (&table, 1);
  print_aig (var, table, output);
  release_aig (&table, var);
  delete_aig_unique_table (table, b_false);
  finalise_memory_management ();
  fclose (output);
}

void
test_print_aig_neg_var ()
{
  FILE *output = fopen ("output/aig_print_neg_var_output.txt", "w");
  AIGUniqueTable *table = NULL;
  AIG *var = NULL;
  init_error_management (stderr);
  init_memory_management ();
  init_aig_id_generation (1);
  table = create_aig_unique_table (8);
  var = invert_aig (var_aig (&table, 1));
  print_aig (var, table, output);
  release_aig (&table, var);
  delete_aig_unique_table (table, b_false);
  finalise_memory_management ();
  fclose (output);
}

void
test_print_aig_x1_and_x2 ()
{
  FILE *output = fopen ("output/aig_print_x1_and_x2_output.txt", "w");
  AIGUniqueTable *table = NULL;
  AIG *and = NULL;
  AIG *x1 = NULL;
  AIG *x2 = NULL;
  init_error_management (stderr);
  init_memory_management ();
  init_aig_id_generation (3);
  table = create_aig_unique_table (8);
  x1 = var_aig (&table, 1);
  x2 = var_aig (&table, 2);
  and = and_aig (&table, x1, x2);
  print_aig (and, table, output);
  release_aig (&table, and);
  release_aig (&table, x1);
  release_aig (&table, x2);
  delete_aig_unique_table (table, b_false);
  finalise_memory_management ();
  fclose (output);
}

void
test_print_aig_x1_nand_x2 ()
{
  FILE *output = fopen ("output/aig_print_x1_nand_x2_output.txt", "w");
  AIGUniqueTable *table = NULL;
  AIG *and = NULL;
  AIG *x1 = NULL;
  AIG *x2 = NULL;
  init_error_management (stderr);
  init_memory_management ();
  init_aig_id_generation (3);
  table = create_aig_unique_table (8);
  x1 = var_aig (&table, 1);
  x2 = var_aig (&table, 2);
  and = invert_aig (and_aig (&table, x1, x2));
  print_aig (and, table, output);
  release_aig (&table, and);
  release_aig (&table, x1);
  release_aig (&table, x2);
  delete_aig_unique_table (table, b_false);
  finalise_memory_management ();
  fclose (output);
}

void
test_print_aig_simple_aig ()
{
  FILE *output = fopen ("output/aig_print_simple_aig_output.txt", "w");
  AIGUniqueTable *table = NULL;
  AIG *and = NULL;
  AIG *and_top = NULL;
  AIG *x1 = NULL;
  AIG *x2 = NULL;
  AIG *x3 = NULL;
  init_error_management (stderr);
  init_memory_management ();
  init_aig_id_generation (4);
  table = create_aig_unique_table (8);
  x1 = var_aig (&table, 1);
  x2 = var_aig (&table, 2);
  x3 = var_aig (&table, 3);
  and = and_aig (&table, x1, x2);
  and_top = and_aig (&table, and, invert_aig(x3)); 
  print_aig (and_top, table, output);
  delete_aig_unique_table (table, b_true);
  finalise_memory_management ();
  fclose (output);
}

void
run_aig_tests ()
{
  run_test (test_create_delete_aig_unique_table);
  run_test (test_var_aig);
  run_test (test_and_aig);
  run_test (test_is_aig_constant);
  run_test (test_invert_aig);
  run_test (test_is_inverted_aig);
  run_test (test_real_address_aig);
  run_test (test_copy_aig);
  run_test (test_release_aig);
  run_test (test_release_aig_recursive);
  run_test (test_aig_ref_counter_overflow);
  run_test (test_aig_unique_table);
  run_test (test_aig_unique_table_enlargement);
  run_test (test_aig_unique_table_max_enlargement);
  run_test (test_aig_unique_table_enlargement_random);
  run_test (test_and_aig_commutative);
  run_test (test_aig_simple_optimisations);
  run_test (test_or_aig);
  run_test (test_imp_aig);
  run_test (test_dimp_aig);
  run_test (test_xor_aig);
  run_test (test_and_aig_releases);
  run_test (test_or_aig_releases);
  run_test (test_imp_aig_releases);
  run_test (test_dimp_aig_releases);
  run_test (test_xor_aig_releases);
  run_test (test_and_aig_array);
  run_test (test_or_aig_array);
  run_test (test_dimp_aig_array);
  run_test (test_xor_aig_array);
  run_test (test_and_aig_array_releases);
  run_test (test_or_aig_array_releases);
  run_test (test_dimp_aig_array_releases);
  run_test (test_xor_aig_array_releases);
  run_test (test_and_aig_va_list);
  run_test (test_or_aig_va_list);
  run_test (test_dimp_aig_va_list);
  run_test (test_xor_aig_va_list);
  run_test (test_and_aig_va_list_releases);
  run_test (test_or_aig_va_list_releases);
  run_test (test_dimp_aig_va_list_releases);
  run_test (test_xor_aig_va_list_releases);
  run_test (test_full_add_aig_1);
  run_test (test_full_add_aig_2);
  run_test (test_full_add_aig_3);
  run_test (test_full_add_aig_4);
  run_test (test_full_add_aig_5);
  run_test (test_full_add_aig_6);
  run_test (test_full_add_aig_7);
  run_test (test_full_add_aig_8);
  run_test (test_full_add_aig_releases);
  run_test (test_ripple_compare_aig_1);
  run_test (test_ripple_compare_aig_2);
  run_test (test_ripple_compare_aig_3);
  run_test (test_ripple_compare_aig_4);
  run_test (test_ripple_compare_aig_5);
  run_test (test_ripple_compare_aig_6);
  run_test (test_ripple_compare_aig_7);
  run_test (test_ripple_compare_aig_8);
  run_test (test_ripple_compare_aig_9);
  run_test (test_ripple_compare_aig_10);
  run_test (test_ripple_compare_aig_11);
  run_test (test_ripple_compare_aig_12);
  run_test (test_ripple_compare_aig_13);
  run_test (test_ripple_compare_aig_14);
  run_test (test_ripple_compare_aig_15);
  run_test (test_ripple_compare_aig_16);
  run_test (test_ripple_compare_aig_17);
  run_test (test_ripple_compare_aig_18);
  run_test (test_ripple_compare_aig_19);
  run_test (test_ripple_compare_aig_20);
  run_test (test_ripple_compare_aig_21);
  run_test (test_ripple_compare_aig_22);
  run_test (test_ripple_compare_aig_23);
  run_test (test_ripple_compare_aig_24);
  run_test (test_ripple_compare_aig_25);
  run_test (test_ripple_compare_aig_26);
  run_test (test_ripple_compare_aig_27);
  run_test (test_ripple_compare_aig_28);
  run_test (test_ripple_compare_aig_29);
  run_test (test_ripple_compare_aig_30);
  run_test (test_ripple_compare_aig_31);
  run_test (test_ripple_compare_aig_32);
  run_test (test_ripple_compare_aig_releases);
  run_test (test_too_many_aigs_error_var);
  check_output ("output/aig_too_many_aigs_error_var_expected.txt",
                "output/aig_too_many_aigs_error_var_output.txt");
  run_test (test_too_many_aigs_error_and);
  check_output ("output/aig_too_many_aigs_error_and_expected.txt",
                "output/aig_too_many_aigs_error_and_output.txt");
  run_test (test_print_aig_constant_true);
  check_output ("output/aig_print_constant_true_expected.txt",
                "output/aig_print_constant_true_output.txt");
  run_test (test_print_aig_constant_false);
  check_output ("output/aig_print_constant_false_expected.txt",
                "output/aig_print_constant_false_output.txt");
  run_test (test_print_aig_var);
  check_output ("output/aig_print_var_expected.txt",
                "output/aig_print_var_output.txt");
  run_test (test_print_aig_neg_var);
  check_output ("output/aig_print_neg_var_expected.txt",
                "output/aig_print_neg_var_output.txt");
  run_test (test_print_aig_x1_and_x2);
  check_output ("output/aig_print_x1_and_x2_expected.txt",
                "output/aig_print_x1_and_x2_output.txt");
  run_test (test_print_aig_x1_nand_x2);
  check_output ("output/aig_print_x1_nand_x2_expected.txt",
                "output/aig_print_x1_nand_x2_output.txt");
  run_test (test_print_aig_simple_aig);
  check_output ("output/aig_print_simple_aig_expected.txt",
                "output/aig_print_simple_aig_output.txt");
}
