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
#include "memory_management.h"
#include "token.h"
#include "bool.h"

static Token *
create_token_private (const char *str, long long int val, int kind,
                      unsigned int line, unsigned int col)
{
  Token *token = (Token *) malloc_c32sat (sizeof (Token));
  token->line = line;
  token->col = col;
  token->kind = kind;
  if (kind == t_ident)
    {
      token->str =
        (char *) malloc_c32sat (sizeof (char) * (strlen (str) + 1));
      strcpy (token->str, str);
    }
  else
    {
      token->str = NULL;
    }
  if (kind == t_integer)
    {
      token->val = val;
    }
  else
    {
      token->val = 0;
    }
  return token;
}

Token *
create_token (TokenKind kind, unsigned int line, unsigned int col)
{
  assert (kind != t_ident && kind != t_integer && line > 0 && col > 0);
  return create_token_private (NULL, 0, kind, line, col);
}

Token *
create_ident_token (const char *str, unsigned int line, unsigned int col)
{
  assert (str != NULL && line > 0 && col > 0);
  return create_token_private (str, 0, t_ident, line, col);
}

Token *
create_integer_token (long long int val, unsigned int line, unsigned int col)
{
  assert (line > 0 && col > 0);
  return create_token_private (NULL, val, t_integer, line, col);
}

void
delete_token (Token * token)
{
  assert (token != NULL);
  if (token->kind == t_ident)
    {
      free_c32sat (token->str, sizeof (char) * (strlen (token->str) + 1));
    }
  free_c32sat (token, sizeof (Token));
}
