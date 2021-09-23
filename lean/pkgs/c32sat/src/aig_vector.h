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
#ifndef _AIG_VECTOR_H_
#define _AIG_VECTOR_H_

#include "aig.h"
#include "bool.h"

/** @brief Represents a vector of 8, 16, 32 or 64 AIGs */
struct AIGVector
{
  /** Vector elements*/
  AIG **aig;
  /** Determines if the AIG vector represents an undefined
   * value as result of undefined behaviour (C99)
   */
  AIG *undefined;
};

typedef struct AIGVector AIGVector;

/** Creates an AIG vector and initialises every AIG
 * to @ref AIG_FALSE.
 */
AIGVector *create_aig_vector ();

/** Deletes an AIG vector from memory. 
 * @param aig_vector The AIG vector which has to be deleted
 */
void delete_aig_vector (AIGVector * aig_vector);

/** Creates a new copy by calling @ref copy_aig for every
 * AIG.
 * @param table The unique table used for managing AIGs
 * @param aig_vector The AIG vector which has to be copied
 * @return The copy of the AIG vector
 */
AIGVector *copy_aig_vector (AIGUniqueTable ** table, AIGVector * aig_vector);

/** Releases all AIGs of the AIG vector.
 * @param table The unique table used for managing AIGs
 * @param aig_vector The corresponding AIG vector.
 * The function @ref release_aig is called for every AIG.
 */
void release_aig_vector (AIGUniqueTable ** table, AIGVector * aig_vector);

/** Transforms an AIG vector into an integer. The elements
 * of the AIG vector have to be @ref AIG_TRUE or @ref AIG_FALSE!
 * @param aig_vector The AIG vector
 * @return Returns the integer result
 */
long long int aig_vector_2_long_long (AIGVector * aig_vector);

/** Transforms an integer into an AIG vector and stores it into 
 * result. The AIG undefined will be ignroed.
 * @param x The integer input
 * @param result The AIG vector into which the result has to be stored
 */
void long_long_2_aig_vector (long long int x, AIGVector * result);

/** Returns an AIG which represents the conjunction of all 
 * 32 AIGs. The AIG undefined will be ignored.
 * @param table The unique table used for managing AIGs
 * @param aig_vector The AIG vector which is used for the conjunction
 * @return The conjunction of all elements
 */
AIG *conjunction_aig_vector (AIGUniqueTable ** table, AIGVector * aig_vector);

/** Returns an AIG which represents the disjunction of all 
 * 32 AIGs. The AIG undefined will be ignored.
 * @param table The unique table used for managing AIGs
 * @param aig_vector The AIG vector which is used for the disjunction
 * @return The disjunction of all elements
 */
AIG *disjunction_aig_vector (AIGUniqueTable ** table, AIGVector * aig_vector);

/** Returns an AIG vector which represents the boolean negation
 * of the operand regarding C semantics of true and false.
 * @param table The unique table used for managing AIGs
 * @param x The operand
 * @return The boolean negation of x
 */
AIGVector *not_aig_vector (AIGUniqueTable ** table, AIGVector * x);

/** Returns an AIG vector which represents the boolean 
 * conjunction of x and y regarding C semantics of true and
 * false.
 * @param table The unique table used for managing AIGs
 * @param x The left operand
 * @param y The right operand
 * @return The conjunction of x and y
 */
AIGVector *and_aig_vector (AIGUniqueTable ** table, AIGVector * x,
                           AIGVector * y);

/** Returns an AIG vector which represents the boolean 
 * disjunction of x and y regarding C semantics of true and
 * false.
 * @param table The unique table used for managing AIGs
 * @param x The left operand
 * @param y The right operand
 * @return The disjunction of x and y
 */
AIGVector *or_aig_vector (AIGUniqueTable ** table, AIGVector * x,
                          AIGVector * y);

/** Returns an AIG vector which represents the boolean 
 * implication of x and y regarding C semantics of true and
 * false.
 * @param table The unique table used for managing AIGs
 * @param x The left operand
 * @param y The right operand
 * @return x => y
 */
AIGVector *imp_aig_vector (AIGUniqueTable ** table, AIGVector * x,
                           AIGVector * y);

/** Returns an AIG vector which represents the boolean 
 * double implication of x and y regarding C semantics of
 * true and false.
 * @param table The unique table used for managing AIGs
 * @param x The left operand
 * @param y The right operand
 * @return x <=> y
 */
AIGVector *dimp_aig_vector (AIGUniqueTable ** table, AIGVector * x,
                            AIGVector * y);

/** Inverts an AIG vector by calling @ref invert_aig
 * for all 32 AIGs.
 * @param aig_vector The AIG vector which has to be inverted
 */
void invert_aig_vector (AIGVector * aig_vector);

/** Returns the bitwise conjunction of the two operands by
 * calling @ref and_aig for every bit of the two operands.
 * @param table The unique table used for managing AIGs
 * @param x The left operand
 * @param y The right operand
 * @return The bitwise conjunction of x and y
 */
AIGVector *band_aig_vector (AIGUniqueTable ** table, AIGVector * x,
                            AIGVector * y);

/** Returns the bitwise disjunction of the two operands by
 * calling @ref or_aig for every bit of the two operands.
 * @param table The unique table used for managing AIGs
 * @param x The left operand
 * @param y The right operand
 * @return The bitwise disjunction of x and y
 */
AIGVector *bor_aig_vector (AIGUniqueTable ** table, AIGVector * x,
                           AIGVector * y);

/** Returns the bitwise exclusive disjunction of the two 
 * operands by calling @ref xor_aig for every bit of the two
 * operands.
 * @param table The unique table used for managing AIGs
 * @param x The left operand
 * @param y The right operand
 * @return The bitwise exclusive disjunction of x and y
 */
AIGVector *bxor_aig_vector (AIGUniqueTable ** table, AIGVector * x,
                            AIGVector * y);

/** Returns an AIG vector which represents the adding of the
 * two operands.
 * @param table The unique table used for managing AIGs
 * @param x The first operand
 * @param y The second operand
 * @return x + y 
 */
AIGVector *add_aig_vector (AIGUniqueTable ** table, AIGVector * x,
                           AIGVector * y);

/** Returns an AIG vector which represents the result of the 
 * unary minus operation.
 * @param table The unique table used for managing AIGs
 * @param x The AIG vector which has to be complemented
 * @return The AIG vector which represents the twos complement
 * of x
 */
AIGVector *unary_minus_aig_vector (AIGUniqueTable ** table, AIGVector * x);

/** Returns an AIG vector which represents the subtraction of the
 * two operands.
 * @param table The unique table used for managing AIGs
 * @param x The first operand
 * @param y The second operand
 * @return x - y
 */
AIGVector *subtract_aig_vector (AIGUniqueTable ** table, AIGVector * x,
                                AIGVector * y);

/** Returns an AIG vector which represents if the two operands 
 * are equal.
 * @param table The unique table used for managing AIGs
 * @param x The first operand
 * @param y The second operand
 * @return x == y
 */
AIGVector *eq_aig_vector (AIGUniqueTable ** table, AIGVector * x,
                          AIGVector * y);

/** Returns an AIG vector which represents if the two operands 
 * are not equal.
 * @param table The unique table used for managing AIGs
 * @param x The first operand
 * @param y The second operand
 * @return x != y
 */
AIGVector *neq_aig_vector (AIGUniqueTable ** table, AIGVector * x,
                           AIGVector * y);

/** Returns an AIG vector which represents if the first operand
 * is less than the second operand.
 * @param table The unique table used for managing AIGs
 * @param x The first operand
 * @param y The second operand
 * @return x < y
 */
AIGVector *less_than_aig_vector (AIGUniqueTable ** table, AIGVector * x,
                                 AIGVector * y);

/** Returns an AIG vector which represents if the first operand
 * is less than or equal the second operand.
 * @param table The unique table used for managing AIGs
 * @param x The first operand
 * @param y The second operand
 * @return x <= y
 */
AIGVector *less_than_or_equal_aig_vector (AIGUniqueTable ** table,
                                          AIGVector * x, AIGVector * y);

/** Returns an AIG vector which represents if the first operand
 * is greater than the second operand.
 * @param table The unique table used for managing AIGs
 * @param x The first operand
 * @param y The second operand
 * @return x > y
 */
AIGVector *greater_than_aig_vector (AIGUniqueTable ** table, AIGVector * x,
                                    AIGVector * y);

/** Returns an AIG vector which represents if the first operand
 * is greater than or equal the second operand.
 * @param table The unique table used for managing AIGs
 * @param x The first operand
 * @param y The second operand
 * @return x >= y
 */
AIGVector *greater_than_or_equal_aig_vector (AIGUniqueTable ** table,
                                             AIGVector * x, AIGVector * y);

/** Shifts an AIG vector left.
 * @param table The unique table used for managing AIGs
 * @param x The AIG vector which has to be shifted
 * @param y The 32 bit and inverer graph which determines
 * for how many bits x should be shifted
 * @return The shifted AIG vector
 */
AIGVector *shift_left_aig_vector (AIGUniqueTable ** table, AIGVector * x,
                                  AIGVector * y);

/** Shifts an AIG vector right.
 * @param table The unique table used for managing AIGs
 * @param x The AIG vector which has to be shifted
 * @param y The 32 bit and inverer graph which determines
 * for how many bits x should be shifted
 * @return The shifted AIG vector
 */
AIGVector *shift_right_aig_vector (AIGUniqueTable ** table, AIGVector * x,
                                   AIGVector * y);

/** Multiplies two AIG vectors.
 * @param table The unique table used for managing AIGs
 * @param x The first AIG vector
 * @param y The second AIG vector
 * @return The resulting AIG vector which represents
 * x * y
 */
AIGVector *multiply_aig_vector (AIGUniqueTable ** table, AIGVector * x,
                                AIGVector * y);

/** Selects an AIG vector depending on the condition. If
 * If the condition is true then the if_case is selected.
 * Otherwise the else_case is selected. You can think of 
 * it as a multiplexer.
 * @param table The unique table used for managing AIGs
 * @param condition The condition determines which case
 * should be selected
 * @param if_case The case which is selected if the 
 * condition is true
 * @param else_case The case which is selected if the 
 * condition is false
 * @return The resulting AIG vector which represents the
 * selection depending on the condition
 */
AIGVector *if_then_else_aig_vector (AIGUniqueTable ** table,
                                    AIGVector * condition,
                                    AIGVector * if_case,
                                    AIGVector * else_case);

/* Divides the first operand by the second operand and 
 * returns the resulting quotient.
 * @param table The unique table used for managing AIGs
 * @param x The first operand
 * @param y The second operand
 * @param return x / y
 */
AIGVector *divide_aig_vector (AIGUniqueTable ** table, AIGVector * x,
                              AIGVector * y);

/* Returns the first operand modulo the second operand.
 * @param table The unique table used for managing AIGs
 * @param x The first operand
 * @param y The second operand
 * @return x % y
 */
AIGVector *modulo_aig_vector (AIGUniqueTable ** table, AIGVector * x,
                              AIGVector * y);

#endif
