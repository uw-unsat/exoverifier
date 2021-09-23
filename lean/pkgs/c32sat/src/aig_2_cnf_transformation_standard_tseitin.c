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
#include "aig.h"
#include "cnf.h"
#include "hash_table.h"
#include "stack.h"
#include "aig_id_generation.h"
#include "aig_2_cnf_transformation_standard_tseitin.h"

#define AIG_2_CNF_TRANSFORMATION_STANDARD_TSEITIN_INITIAL_HASHTABLE_POWER 10

static unsigned int
compute_hash_value_aig_2_cnf_standard_tseitin (void *key)
{
  assert (!is_inverted_aig ((AIG *) key));
  assert (((AIG *) key)->id > 0);
  return (unsigned int) ((AIG *) key)->id;
}

static unsigned int
compute_equals_aig_2_cnf_standard_tseitin (void *key1, void *key2)
{
  return key1 == key2;
}

CNF *
aig_2_cnf_standard_tseitin (AIG * aig, int first_free_id)
{
  int x = 0;
  int y = 0;
  int z = 0;
  CNF *cnf = NULL;
  HashTable *table = NULL;
  Stack *stack = NULL;
  AIG *cur = NULL;
  AIG *left = NULL;
  AIG *right = NULL;
  assert (!is_aig_constant (aig) && first_free_id > 0);
  init_aig_id_generation (first_free_id);
  cnf = create_cnf ();
  /* Generate constraint for output. Output has to be true */
  add_cnf (cnf, retrieve_aig_id (aig));
  add_cnf (cnf, 0);
  /* If the root is an and gate then start generating constraints
   * for every and gate in the AIG */
  cur = aig_real_address (aig);
  if (is_aig_and (cur))
    {
      table = create_hash_table
        (AIG_2_CNF_TRANSFORMATION_STANDARD_TSEITIN_INITIAL_HASHTABLE_POWER,
         compute_hash_value_aig_2_cnf_standard_tseitin,
         compute_equals_aig_2_cnf_standard_tseitin, NULL);
      stack = create_stack ();
      push_stack (stack, (void *) cur);
      while ((cur = (AIG *) pop_stack (stack)) != NULL)
        {
          assert (!is_inverted_aig (cur));
          left = aig_left_child (cur);
          right = aig_right_child (cur);
          x = retrieve_aig_id (cur);
          y = retrieve_aig_id (left);
          z = retrieve_aig_id (right);
          add_cnf (cnf, -x);
          add_cnf (cnf, y);
          add_cnf (cnf, 0);
          add_cnf (cnf, -x);
          add_cnf (cnf, z);
          add_cnf (cnf, 0);
          add_cnf (cnf, -y);
          add_cnf (cnf, -z);
          add_cnf (cnf, x);
          add_cnf (cnf, 0);
          /* We have to visit the children if they represent
           * an and gate */
          left = aig_real_address (left);
          right = aig_real_address (right);
          if (is_aig_and (right))
            {
              if (lookup_hash_table (&table, (void *) right) == NULL)
                {
                  insert_data_hash_table (&table, (void *) right,
                                          (void *) right);
                  push_stack (stack, (void *) right);
                }
            }
          if (is_aig_and (left))
            {
              if (lookup_hash_table (&table, (void *) left) == NULL)
                {
                  insert_data_hash_table (&table, (void *) left,
                                          (void *) left);
                  push_stack (stack, (void *) left);
                }
            }
        }
      delete_stack (stack);
      delete_hash_table (table, b_false);
    }
  return cnf;
}
