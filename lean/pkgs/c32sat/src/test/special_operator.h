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
#ifndef _SPECIAL_OPERATOR_H_
#define _SPECIAL_OPERATOR_H_

#include "../bool.h"

/** This function defines the expected behaviour of the left 
 * shift operator for some special test cases which is not 
 * fully defined by the ISO C99 standard. This function makes
 * shure that the test constraints do not depend on the platform
 * where the testsuite runs.
 * @param x The left operand
 * @param y The right operand
 * @param number_of_bits The number of bits
 * @return The implementation defined result of x << y
 */
int shift_left_special_operator (const int x, const int y,
                                 const int number_of_bits);

/** This function defines the expected behaviour of the right 
 * shift operator for some special test cases which is not 
 * fully defined by the ISO C99 standard. This function makes 
 * shure that the test constraints do not depend on the platform
 * where the testsuite runs.
 * @param x The left operand
 * @param y The right operand
 * @param number_of_bits The number of bits
 * @return The implementation defined result of x >> y
 */
int shift_right_special_operator (const int x, const int y,
                                  const int number_of_bits);

/** This function defines the expected behaviour of the addition
 * operator for some special test cases which is not 
 * fully defined by the ISO C99 standard. The standard does not
 * define what the result looks like if there is an integer
 * overflow. This function makes shure that the test constraints
 * do not depend on the platform where the testsuite runs.
 * @param x The left operand
 * @param y The right operand
 * @param number_of_bits The number of bits
 * @return The implementation defined result of x + y
 */
int add_special_operator (const int x, const int y, const int number_of_bits);

/** This function can be used to add two binary integers.
 * @param x The first binary integer
 * @param y The second binary integer
 * @param result The result of the adding
 * @param number_of_bits The number of bits
 */
void binary_add_special_operator (const int *x, const int *y, int *result,
                                  const int number_of_bits);

/** This function defines the expected behaviour of the subtraction
 * operator for some special test cases which is not 
 * fully defined by the ISO C99 standard. The standard does not
 * define what the result looks like if there is an integer
 * overflow. This function makes shure that the test constraints
 * do not depend on the platform where the testsuite runs.
 * @param x The left operand
 * @param y The right operand
 * @param number_of_bits The number of bits
 * @return The implementation defined result of x - y
 */
int subtract_special_operator (const int x, const int y,
                               const int number_of_bits);

/** This function defines the expected behaviour of the
 * multiplication operator for some special test cases which
 * is not fully defined by the ISO C99 standard. The standard
 * does not what the result looks like if there is an integer
 * overflow. This function makes shure that the test constraints
 * do not depend on the platform where the testsuite runs.
 * @param x The left operand
 * @param y The right operand
 * @param number_of_bits The number of bits
 * @return The implementation defined result of x * y
 */
int multiply_special_operator (const int x, const int y,
                               const int number_of_bits);

#endif
