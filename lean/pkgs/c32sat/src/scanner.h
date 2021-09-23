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
#ifndef _SCANNER_H_
#define _SCANNER_H_

#include <stdio.h>
#include "token.h"

/** Maximum length of an identifier */
#define MAX_IDENT_LENGTH 256
/** Maximum value of a 64 bit integer */
#define MAX_INT_VAL_64 9223372036854775807ll
/** Maximum value of a 32 bit integer */
#define MAX_INT_VAL_32 2147483647
/** Maximum value of a 16 bit integer */
#define MAX_INT_VAL_16 32767
/** Maximum value of an 8 bit integer */
#define MAX_INT_VAL_8 127
/** Maximum value of a 4 bit integer */
#define MAX_INT_VAL_4 7
/** Maximum string length of a 64 bit integer */
#define MAX_INT_STRING_LENGTH_64 19
/** Maximum string length of a 32 bit integer */
#define MAX_INT_STRING_LENGTH_32 10
/** Maximum string length of a 16 bit integer */
#define MAX_INT_STRING_LENGTH_16 5
/** Maximum string length of an 8 bit integer */
#define MAX_INT_STRING_LENGTH_8 3
/** Maximum string length of a 4 bit integer */
#define MAX_INT_STRING_LENGTH_4 1

/** @brief Represents a scanner. */
struct Scanner
{
  /** The input file which is used for reading characters */
  FILE *input;
  /** The current character */
  int cur;
  /** The current line in the input file */
  unsigned int line;
  /** The current column in the input file */
  unsigned int col;
  /** Maximum integer value */
  long long int max_int_val;
  /** Maximum integer string length */
  int max_int_string_length;
};

typedef struct Scanner Scanner;

/**
 * Creates a scanner, initialises it and returns it.
 * @param input The input file from which the scanner
 * reads the input
 * @return The resulting scanner
 */
Scanner *create_scanner (FILE * input);

/** Delets a scanner from memory.
 * @param scanner The scanner which has to be deleted
 */
void delete_scanner (Scanner * scanner);

/** Scans the input file and returns the next token. If the
 * end of the file is reached then a special token with kind
 * @ref t_eof will be returned.
 * @param scanner The scanner which has to be used
 * @return The next generated token
 */
Token *scan (Scanner * scanner);

#endif
