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
#include <stdlib.h>
#include "test_logging.h"
#include "file_comparison.h"

static const char *bash_green = "\e[1;32m";
static const char *bash_blue = "\e[1;34m";
static const char *bash_red = "\e[1;31m";
static const char *bash_default = "\e[0;39m";

int g_bash;
int g_num_tests;
int g_outputs_compared;
int g_outputs_failed;

void
init_test_logging (int bash)
{
  g_bash = bash;
  g_num_tests = 0;
  g_outputs_compared = 0;
  g_outputs_failed = 0;
}

void
run_test_case (void (*funcp) (), char *name)
{
  g_num_tests++;
  printf (" Running %s ...", name);
  fflush (stdout);
  funcp ();
  if (g_bash)
    {
      printf ("  %s[ %sOK %s]%s\n", bash_blue, bash_green, bash_blue,
              bash_default);
    }
  else
    {
      printf ("  [ OK ]\n");
    }
}

void
check_output (char *expected, char *output)
{
  FilesEqualResult eq_result = equal_files (expected, output);
  g_outputs_compared++;
  printf ("  Comparing output ...");
  if (eq_result == fer_equal)
    {
      if (g_bash)
        {
          printf ("  %s[ %sOK %s]%s\n", bash_blue, bash_green, bash_blue,
                  bash_default);
        }
      else
        {
          printf ("  [ OK ]\n");
        }
    }
  else
    {
      g_outputs_failed++;
      if (eq_result == fer_not_equal)
        {
          if (g_bash)
            {
              printf ("  %sFAILED!!!%s\n", bash_red, bash_default);
            }
          else
            {
              printf ("  FAILED!!!\n");
            }
        }
      else
        {
          if (g_bash)
            {
              printf ("  %sIO ERROR!!!%s\n", bash_red, bash_default);
            }
          else
            {
              printf ("  IO ERROR!!!\n");
            }
        }
    }
}

int
get_num_tests ()
{
  return g_num_tests;
}

int
get_outputs_compared ()
{
  return g_outputs_compared;
}

int
get_outputs_failed ()
{
  return g_outputs_failed;
}
