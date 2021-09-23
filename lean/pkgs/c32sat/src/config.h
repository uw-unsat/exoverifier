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
#ifndef _CONFIG_H_
#define _CONFIG_H_

#include "bool.h"

enum AppMode
{
  am_sat,
  am_sat_ua,
  am_taut,
  am_always_def,
  am_always_undef
};

typedef enum AppMode AppMode;

/** Default application mode */
#define CONFIG_DEFAULT_APP_MODE am_sat
/** Default number of bits which is used in C32SAT */
#define CONFIG_DEFAULT_NUMBER_OF_BITS 32
/** Starting approximation bit width */
#define CONFIG_STARTING_APPROXIMATION_BIT_WIDTH 1
/** Default number of supported variables */
#define CONFIG_DEFAULT_NUMBER_OF_SUPPORTED_VARIABLES 1000000000
/** Default number of supported AIGs */
#define CONFIG_DEFAULT_NUMBER_OF_SUPPORTED_AIGS 2147483647
/** Default number of supported CNF clauses */
#define CONFIG_DEFAULT_NUMBER_OF_SUPPORTED_CNF_CLAUSES 2147483647
/** Maximum long long value */
#define LONG_LONG_MAX_VAL 9223372036854775807LL
/** Minimum long long value */
#define LONG_LONG_MIN_VAL (-9223372036854775807LL -1)

/** Application mode */
extern AppMode ext_app_mode;

/** Number of bits which is used in C32SAT. Default value is 32. 
 * Value must be a power of 2! */
extern int ext_number_of_bits;

/** Approximation bit width (only in am_sat_oa) */
extern int ext_approx_number_of_bits;

/** Number of supported variables in the input */
extern int ext_number_of_supported_variables;

/** Number of supported AIGs */
extern int ext_number_of_supported_aigs;

/** Number of supported CNF clauses */
extern int ext_number_of_supported_cnf_clauses;

/** Determines if integer overflow is allowed */
extern Bool ext_allow_overflow;

/** Determines if two level AIG optimization is on or off */
extern Bool ext_two_level_opt;

#endif
