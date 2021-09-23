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
#ifndef _AIG_H_
#define _AIG_H_

#include <stdarg.h>
#include <stdio.h>
#include "bool.h"

/* ATTENTION: The least significant bit of the address of an
 * AIG is used to store the information if the edge to this AIG
 * is inverted or not. Be sure to get the real address of an
 * AIG by calling @ref aig_real_address before you derefence 
 * it. See also @ref is_inverted_aig and @ref invert_aig.
 */

/** @brief Represents an and inverter graph. */
struct AIG
{
  /** The id of the AIG */
  int id;
  /** The children of the AIG. 
   * Only used if graph represents an and gate. 
   */
  struct AIG *children[2];
  /** The hash value*/
  unsigned int hash;
  /** The reference counter */
  unsigned int refs;
  /** The next AIG in the hash chain */
  struct AIG *next;
};

typedef struct AIG AIG;

/** The constant AIG false. */
#define AIG_FALSE (( AIG *) 0ul)
/** The constant AIG true */
#define AIG_TRUE (( AIG *) 1ul)
/** Checks if aig is @ref AIG_TRUE or @ref AIG_FALSE. */
#define is_aig_constant(aig) (((aig) == AIG_TRUE) || ((aig) == AIG_FALSE))
/** Inverts the edge to an AIG. */
#define invert_aig(aig) (( AIG *) (1ul ^ (unsigned long int) (aig)))
/** Checks if an edge to an AIG is inverted. */
#define is_inverted_aig(aig) (1ul & (unsigned long int) (aig))
/** Returns the real address of an AIG. */
#define aig_real_address(aig) (( AIG *) (~1ul & (unsigned long int) (aig)))
/** Checks if AIG represents a variable. 
 * AIG may not be constant or inverted!
 */
#define is_aig_var(aig) ((aig)->children[0] == NULL)
/** Checks if AIG represents the boolean and operator.
 * AIG may not be constant or inverted!
 */
#define is_aig_and(aig) ((aig)->children[0] != NULL)
/** Gets the left child. AIG may not be 
 * a variable, constant or inverted! */
#define aig_left_child(aig) ((aig)->children[0])
/** Gets the right child. AIG may not be 
 * a variable, constant or inverted! */
#define aig_right_child(aig) ((aig)->children[1])

/** @brief Represents an AIG unique table. 
 * This table is responsible for realising structural
 * sharing by using hash values.
 */
struct AIGUniqueTable
{
  /** The size of the table represents the number
   *  of hash collision chains */
  int size;
  /** The number of boolean variables */
  int num_vars;
  /** The number of boolean ands */
  int num_ands;
  /** @ref b_true if a reference counter overflow occured and 
   * @ref b_false if not. If a reference counter overflow 
   * occured then the entries of the table can only be deleted
   * by calling @ref delete_aig_unique_table.
   */
  Bool ref_overflow_occured;
  /** The hash collision chains */
  AIG **chains;
};

typedef struct AIGUniqueTable AIGUniqueTable;

/** Maximum power of the AIG unique table size */
#define AIG_UNIQUE_TABLE_MAX_POWER 24
/** Maximum size of the AIG unique table */
#define AIG_UNIQUE_TABLE_MAX_SIZE (1 << AIG_UNIQUE_TABLE_MAX_POWER)

/** Creates an AIG unique table.
 * @param power The power of the table. A power of 4 means 
 * for example that the size of the table is 1 << 4 = 16.
 * The minimum of power and @ref AIG_UNIQUE_TABLE_MAX_POWER 
 * will be used.
 */
AIGUniqueTable *create_aig_unique_table (int power);

/** Deletes an AIG unique table from memory.
 * @param table The table which has to be deleted
 * @param delete_entries Determines if the entries of the
 * table als have to be deleted.
 */
void delete_aig_unique_table (AIGUniqueTable * table, Bool delete_entries);

/** Returns an AIG which represents a boolean variable. If the
 * the unique table doesn't already contain the graph then
 * a new graph will be created, hashed and returned. If the
 * unique table already contains the graph then no new graph
 * will be created. The pointer to the graph which is 
 * already in the unique table will be returned instead
 * and the reference counter of the graph will be incremented.
 * @param table The unique table used for managing AIGs
 * @param id The id of the variable
 * @return The AIG which represents a boolean variable or
 * @ref AIG_FALSE if too many AIG nodes have been created. See
 * @ref ext_too_many_aigs_error_occured.
 */
AIG *var_aig (AIGUniqueTable ** table, int id);

/** Returns an AIG which represents the boolean conjunction 
 * of left and right. If the the unique table doesn't already
 * contain the graph then a new graph will be created, hashed
 * and returned. If the unique table already contains the graph
 * then no new graph will be created. The pointer to the graph
 * which is already in the unique table will be returned instead. 
 * If simplification is possible it will be done.
 * @param table The unique table used for managing AIGs
 * @param left The left operand of the operator
 * @param right The right operand of the operator
 * @return The AIG which represents the boolean and operator or
 * @ref AIG_FALSE if too many AIG nodes have been created. See
 * @ref ext_too_many_aigs_error_occured. 
 */
AIG *and_aig (AIGUniqueTable ** table, AIG * left, AIG * right);

/** Returns an AIG which represents the boolean
 * disjunction of left and right.
 * @param table The unique table used for managing AIGs
 * @param left The left operand of the operator
 * @param right The right operand of the operator
 */
AIG *or_aig (AIGUniqueTable ** table, AIG * left, AIG * right);

/** Returns an AIG which represents the boolean
 * implication of left and right.
 * @param table The unique table used for managing AIGs
 * @param left The left operand of the operator
 * @param right The right operand of the operator
 */
AIG *imp_aig (AIGUniqueTable ** table, AIG * left, AIG * right);

/** Returns an AIG which represents the boolean
 * double implication of left and right.
 * @param table The unique table used for managing AIGs
 * @param left The left operand of the operator
 * @param right The right operand of the operator
 */
AIG *dimp_aig (AIGUniqueTable ** table, AIG * left, AIG * right);

/** Returns an AIG which represents the exclusive
 * disjunction of left and right.
 * @param table The unique table used for managing AIGs
 * @param left The left operand of the operator
 * @param right The right operand of the operator
 */
AIG *xor_aig (AIGUniqueTable ** table, AIG * left, AIG * right);

/** Copies an AIG. The function increments the reference counter
 * of the AIG.
 * @param table The unique table used for managing AIGs
 * @param aig The graph which has to be copied
 */
AIG *copy_aig (AIGUniqueTable ** table, AIG * aig);

/** Releases an AIG. The function decrements the reference
 * counter. If the counter reaches 0 then the AIG will be 
 * deleted from the table and from memory. If the counter 
 * reaches 0 and there are children then the reference counter 
 * of the children will be decremented and so on.
 * @param table The unique table used for managing AIGs
 * @param aig The graph which has to be released
 */
void release_aig (AIGUniqueTable ** table, AIG * aig);

/** Returns an AIG which represents the conjunction of the 
 * array using @ref and_aig.
 * @param table The unique table used for managing AIGs
 * @param aigs The array of AIGs
 * @param size The size of the array
 */
AIG *and_aig_array (AIGUniqueTable ** table, AIG ** aigs, int size);

/** Returns an AIG which represents the disjunction of the
 *  array using @ref or_aig.
 * @param table The unique table used for managing AIGs
 * @param aigs The array of AIGs
 * @param size The size of the array
 */
AIG *or_aig_array (AIGUniqueTable ** table, AIG ** aigs, int size);

/** Returns an AIG which represents if all AIGs of the array
 * are equal. The function uses @ref dimp_aig. 
 * @param table The unique table used for managing AIGs
 * @param aigs The array of AIGs
 * @param size The size of the array
 */
AIG *dimp_aig_array (AIGUniqueTable ** table, AIG ** aigs, int size);

/** Returns an AIG which represents the exclusive disjunction
 * of the array using @ref xor_aig.
 * @param table The unique table used for managing AIGs
 * @param aigs The array of AIGs
 * @param size The size of the array
 */
AIG *xor_aig_array (AIGUniqueTable ** table, AIG ** aigs, int size);

/** Returns an AIG which represents the conjunction of the 
 * variadic list using @ref and_aig.
 * @param table The unique table used for managing AIGs
 * @param num_aigs The number of AIGs in the list
 */
AIG *and_aig_va_list (AIGUniqueTable ** table, int num_aigs, ...);

/** Returns an AIG which represents the disjunction of the variadic
 * list using @ref or_aig.
 * @param table The unique table used for managing AIGs
 * @param num_aigs The number of AIGs in the list
 */
AIG *or_aig_va_list (AIGUniqueTable ** table, int num_aigs, ...);

/** Returns an AIG which represents if all AIGs of the
 * variadic list are equal. The function uses @ref dimp_aig. 
 * @param table The unique table used for managing AIGs
 * @param num_aigs The number of AIGs in the list
 */
AIG *dimp_aig_va_list (AIGUniqueTable ** table, int num_aigs, ...);

/** Returns an AIG which represents the excklusive disjunction of 
 * the variadic list using @ref xor_aig.
 * @param table The unique table used for managing AIGs
 * @param num_aigs The number of AIGs in the list
 */
AIG *xor_aig_va_list (AIGUniqueTable ** table, int num_aigs, ...);

/** Represents a full adder which operates on AIGs.
 * @param table The unique table used for managing AIGs
 * @param x The first input of the adder
 * @param y The second input of the adder
 * @param cin The carry input
 * @param cout The resulting carry output
 * @return The result of the adding
 */
AIG *full_add_aig (AIGUniqueTable ** table, AIG * x,
                   AIG * y, AIG * cin, AIG ** cout);

/** This function can be used to compare two vectors of AIGs. Use
 * it to compare the vectors element by element.
 * @param table The unique table used for managing AIGs
 * @param x The element of the first array
 * @param y The element of the second array
 * @param lt_in Determines if the previous compare 
 * result was "less than"
 * @param eq_in Determines if the previous compare 
 * result was "equal"
 * @param gt_in Determines if the previous compare
 * result was "greater than"
 * @param lt_out Determines if the current compare 
 * result is "less than"
 * @param eq_out Determines if the current compare 
 * result is "equal"
 * @param gt_out Determines if the current compare 
 * result is "greater than"  
 */
void ripple_compare_aig (AIGUniqueTable ** table, AIG * x,
                         AIG * y, AIG * lt_in, AIG * eq_in,
                         AIG * gt_in, AIG ** lt_out,
                         AIG ** eq_out, AIG ** gt_out);

void print_aig (AIG * aig, AIGUniqueTable * table, FILE * output);

#endif
