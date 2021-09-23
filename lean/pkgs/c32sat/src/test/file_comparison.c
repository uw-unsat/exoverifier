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
#include <stdio.h>
#include "file_comparison.h"

FilesEqualResult
equal_files (char *expected, char *output)
{
  FILE *fexpected = NULL;
  FILE *foutput = NULL;
  FilesEqualResult result = fer_equal;
  char c1 = 0;
  char c2 = 0;
  fexpected = fopen (expected, "r");
  if (fexpected == NULL)
    {
      return fer_io_error;
    }
  foutput = fopen (output, "r");
  if (foutput == NULL)
    {
      fclose (fexpected);
      return fer_io_error;
    }
  while (result == fer_equal && c1 != EOF && c2 != EOF)
    {
      c1 = fgetc (fexpected);
      c2 = fgetc (foutput);
      if (c1 != c2)
        {
          result = fer_not_equal;
          break;
        }
    }
  if (result == fer_equal)
    {
      if (c1 != EOF || c2 != EOF)
        {
          result = fer_not_equal;
        }
    }
  fclose (fexpected);
  fclose (foutput);
  return result;
}
