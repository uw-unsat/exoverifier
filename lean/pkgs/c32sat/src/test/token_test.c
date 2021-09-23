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
#include "token_test.h"
#include "test_logging.h"
#include "../token.h"
#include "../memory_management.h"

void
test_create_delete_token ()
{
  Token *t = NULL;
  init_memory_management ();
  t = create_token (t_eq, 3, 4);
  assert (t->kind == t_eq);
  assert (t->line == 3);
  assert (t->col == 4);
  assert (t->str == 0);
  assert (t->val == 0);
  delete_token (t);
  t = create_ident_token ("test", 2, 10);
  assert (t->kind == t_ident);
  assert (t->line == 2);
  assert (t->col == 10);
  assert (strcmp(t->str, "test") == 0);
  assert (t->val == 0);
  delete_token (t);
  t = create_integer_token (27, 1, 5);
  assert (t->kind == t_integer);
  assert (t->line == 1);
  assert (t->col == 5);
  assert (t->str == NULL);
  assert (t->val == 27);
  delete_token(t);
  finalise_memory_management ();
}

void
run_token_tests ()
{
  run_test (test_create_delete_token);
}
