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
#ifndef _AIG_TRANSFORMEATION_H_
#define _AIG_TRANSFORMEATION_H_

#include "aig.h"
#include "cnf.h"

/** @brief Represents an AIG to CNF transformer. */
struct AIG2CNFTransformer
{
  /** The name of the transformer */
  char *name;
  /** The function which transforms an AIG into CNF */
  CNF *(*ptr_transform_aig_2_cnf) (AIG *, int);
};

typedef struct AIG2CNFTransformer AIG2CNFTransformer;

/** Creates an AIG to CNF transformer.
 * @param name The name of the transformer
 * @param ptr_transform_aig_2_cnf The transformation function
 * @return The resulting AIG to CNF transformer
 */
AIG2CNFTransformer *create_aig_2_cnf_transformer (char *name,
                                                  CNF *
                                                  (*ptr_transform_aig_2_cnf)
                                                  (AIG *, int));

/** Deletes an AIG to CNF transformer from memory
 * @param transformer The transformer which has to be deleted from memory
 */
void delete_aig_2_cnf_transformer (AIG2CNFTransformer * transformer);

/** Returns an array of the currently installed transformation
 * components. The size of the array is stored in the variable
 * size.
 * @param size This parameter is used to store the size of the 
 * array
 * @return The currently installed transformation components
 */
AIG2CNFTransformer **create_aig_2_cnf_transformers (int *size);

/** Deletes the array of the currently installed transformation
 * components from memory.
 * @param transformers The array of transformation components which has to
 * be deleted from memory
 * @param size The size of the array
 */
void delete_aig_2_cnf_transformers (AIG2CNFTransformer ** transformers,
                                    int size);

/** Transforms an and inverter graph into conjunctive normal
 * form.
 * @param aig The AIG which has to be transformed
 * @param first_free_id The first free id which can be used for 
 * the nodes which represent the boolean and gate
 * @param transformer The transformation component which is
 * used
 * @return The resulting conjunctive normal form
 */
CNF *transform_aig_2_cnf (AIG * aig, int first_free_id,
                          AIG2CNFTransformer * transformer);

#endif
