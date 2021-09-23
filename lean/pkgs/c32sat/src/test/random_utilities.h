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
#ifndef _RANDOM_UTILITIES_H_
#define _RANDOM_UTILITIES_H_

/** Inits the random utilities. */
void init_random_utilites ();

/** Returns if the the random utilities are initialised. */
int is_initialised_random_utilities ();

/** Runs a void function which takes an integer as parameter
 * with random numbers.
 * @param f_ptr The function which should be run
 * @param times The number of calls
 */
void run_void_int_function_random (void (*f_ptr) (int), int times);

/** Runs a void function which takes two integers as parameters
 * with random numbers.
 * @param f_ptr The function which should be run
 * @param times The number of calls
 */
void run_void_int_int_function_random (void (*f_ptr) (int, int), int times);

/** Runs a void function which takes two integers as parameters
 * with random numbers. The random number which will be passed
 * to the function as second argument will never be zero.
 * @param f_ptr The function which should be run
 * @param times The number of calls
 */
void
run_void_int_int_function_random_second_not_zero (void (*f_ptr) (int, int),
                                                  int times);

/** Runs a void function which takes three integers as parameters
 * with random numbers.
 * @param f_ptr The function which should be run
 * @param times The number of calls
 */
void run_void_int_int_int_function_random (void (*f_ptr) (int, int, int),
                                           int times);

#endif
