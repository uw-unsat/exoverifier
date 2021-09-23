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
#include "aig_transformation.h"
#include "aig.h"
#include "memory_management.h"
#include "cnf.h"
#include "aig_2_cnf_transformation_standard_tseitin.h"

AIG2CNFTransformer *
create_aig_2_cnf_transformer (char *name,
                              CNF * (*ptr_transform_aig_2_cnf) (AIG *, int))
{
  AIG2CNFTransformer *transformer = NULL;
  assert (name != NULL && ptr_transform_aig_2_cnf != NULL);
  transformer =
    (AIG2CNFTransformer *) malloc_c32sat (sizeof (AIG2CNFTransformer));
  transformer->name =
    (char *) malloc_c32sat (sizeof (char) * (strlen (name) + 1));
  strcpy (transformer->name, name);
  transformer->ptr_transform_aig_2_cnf = ptr_transform_aig_2_cnf;
  return transformer;
}

void
delete_aig_2_cnf_transformer (AIG2CNFTransformer * transformer)
{
  assert (transformer != NULL && transformer->name != NULL);
  free_c32sat (transformer->name,
               sizeof (char) * (strlen (transformer->name) + 1));
  free_c32sat (transformer, sizeof (AIG2CNFTransformer));
}

AIG2CNFTransformer **
create_aig_2_cnf_transformers (int *size)
{
  AIG2CNFTransformer **transformers = NULL;
  assert (size != NULL);
  transformers =
    (AIG2CNFTransformer **) malloc_c32sat (sizeof (AIG2CNFTransformer *));
  *size = 1;
  transformers[0] =
    create_aig_2_cnf_transformer ("aig_2_cnf_standard_tseitin",
                                  aig_2_cnf_standard_tseitin);
  return transformers;
}

void
delete_aig_2_cnf_transformers (AIG2CNFTransformer ** transformers, int size)
{
  int i = 0;
  assert (size > 0);
  for (i = 0; i < size; i++)
    {
      delete_aig_2_cnf_transformer (transformers[i]);
    }
  free_c32sat (transformers, sizeof (AIG2CNFTransformer *) * size);
}

CNF *
transform_aig_2_cnf (AIG * aig, int first_free_id,
                     AIG2CNFTransformer * transformer)
{
  assert (aig != NULL && first_free_id > 0 && transformer != NULL);
  return transformer->ptr_transform_aig_2_cnf (aig, first_free_id);
}
