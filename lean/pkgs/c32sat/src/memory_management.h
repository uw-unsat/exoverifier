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
#ifndef _MEMORY_MANAGEMENT_H_
#define _MEMORY_MANAGEMENT_H_

#include <stdlib.h>
#include "bool.h"

/** Inits the memory management. Before this function is called
 *  the function @ref init_error_management has to be called.
 *  The @ref init_memory_management function has to be called
 *  before calling any other function of this module! The only
 *  exception is @ref is_initialised_memory_management. */
void init_memory_management ();

/** Finalises the memory management and checks if it was
 *  successful in the debug mode.  */
void finalise_memory_management ();

/** Checks if the memory management is initialisied
 * @return @ref b_true if initialised and @ref b_false if not
 */
Bool is_initialised_memory_management ();

/** Allocates memory for nbytes * num bytes and returns it.
 * @param num_bytes The number of bytes which has to be
 * allocated
 * @return The allocated memory
 */
void *malloc_c32sat (size_t num_bytes);

/** Changes the size of already allocated memory.
 * @param ptr The ptr to the memory location
 * @param old_num_bytes The old size in bytes
 * @param num_bytes The new size in bytes
 * @return The reallocated memory
 */
void *realloc_c32sat (void *ptr, size_t old_num_bytes, size_t num_bytes);

/** Frees the specified memory
 * @param ptr The pointer to the place in memory which has to
 * be freed.
 * @param num_bytes_freed The number of bytes which are freed.
 */
void free_c32sat (void *ptr, size_t num_bytes_freed);

/** Returns the maximum of memory usage during C32SAT in bytes.
 * @return The maximum of memory usage during C32SAT in bytes
 */
long long int get_max_memory_used ();

#endif
