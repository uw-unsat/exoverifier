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
#include "aig_id_generation.h"
#include "aig.h"
#include "bool.h"
#include "hash_table.h"
#include "stack.h"

#define AIG_ID_GENERATION_INITIAL_HASHTABLE_POWER 10

static int g_id = 0;

void
init_aig_id_generation (int first_free_id)
{
  assert (first_free_id > 0);
  g_id = first_free_id;
}

int
retrieve_aig_id (AIG * aig)
{
  AIG *real_aig = NULL;
  Bool inverted = b_false;
  assert (g_id > 0 && aig != NULL && !is_aig_constant (aig));
  if (is_inverted_aig (aig))
    {
      inverted = b_true;
    }
  real_aig = aig_real_address (aig);
  if (real_aig->id == 0)
    {
      real_aig->id = g_id++;
    }
  return inverted ? -real_aig->id : real_aig->id;
}

int
get_next_free_aig_id ()
{
  return g_id;
}
