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
#ifndef _C32SAT_MATH_H_
#define _C32SAT_MATH_H_

/** Computes the minimum of x and y */
#define min_c32sat_math(x,y) ((x) < (y) ? (x):(y))
/** Computes the maximum of x and y */
#define max_c32sat_math(x,y) ((x) > (y) ? (x):(y))

/** Computes the logarithm to base two.
 * @param x The value for which the logarithm has to be computed
 * @return The logarithm to base two of x
 */
int log2_c32sat_math (int x);

/** Computes 2 ^ exp.
 * @param exp The exponent
 * @return 2 ^ exp
 */
long long int pow2_c32sat_math (int exp);

/** Computes 10 ^ exp.
 * @param exp The exponent
 * @return 10 ^ exp as unsigned long long
 */
unsigned long long int pow10_ull_c32sat_math (int exp);

/** Converts a binary vector into a long long.
 * @param bin The binary vector
 * @param number_of_bits The number of bits
 * @return The long long result
 */
long long int bin_2_long_long_c32sat_math (const int *bin, int number_of_bits);

/** Converts a long long into a binary vector.
 * @param x The long long which has to be converted
 * @param result The binary result
 * @param number_of_bits The number of bits
 */
void long_long_2_bin_c32sat_math (long long int x, int *result,
                                  int number_of_bits);

/** Converts a binary vector into a hexadecimal string.
 * @param bin The binary vector
 * @param number_of_bits The number of bits
 * @return The hexadecimal result
 */     
char *bin_2_hex_c32sat_math (const int *bin, int number_of_bits);                                                                   

#endif
