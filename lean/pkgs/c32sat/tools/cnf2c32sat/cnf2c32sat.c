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
#include <ctype.h>

void invalid_cnf(){
  printf("Invalid cnf format\n");
  exit (EXIT_FAILURE);
}

void print_var(int var) {
  if (var < 0){
    putchar('!');
  }
  printf("x%d", abs(var));	
}

int main(int argc, char **argv){
  int cur = 0;
  unsigned int i = 0;
  unsigned int num_vars = 0;
  unsigned int num_clauses = 0;
  if (argc != 1){
  	printf("Usage: cnf2c32sat\n");
  	return EXIT_FAILURE;
  }
  cur = getchar();
  while (cur != EOF && cur != 'p'){
    if (cur == 'c'){
      do {
        cur = getchar();
      } while (cur != '\n' && cur != EOF);
    }
    if (cur != EOF){
      cur = getchar();
    }
  }
  if (cur == EOF){
  	invalid_cnf();
  }
  cur = getchar();
  while (isspace(cur)){
  	cur = getchar();
  }
  if (cur != 'c'){
  	invalid_cnf();
  }
  cur = getchar();
  while (isspace(cur)){
  	cur = getchar();
  }  
  if (cur != 'n'){
  	invalid_cnf();
  }  
  cur = getchar();
  while (isspace(cur)){
  	cur = getchar();
  } 
  if (cur != 'f'){
  	invalid_cnf();
  }
  cur = getchar();
  if (scanf("%u", &num_vars) == EOF){
  	invalid_cnf();
  }
  if (scanf("%u", &num_clauses) == EOF){
    invalid_cnf();
  }
  printf("/* CNF: %u variabes and %u clauses */\n", num_vars, num_clauses);
  for (i = 0; i < num_clauses; i++){
  	putchar('(');
  	if (scanf("%d", &cur) == EOF) {
  	  invalid_cnf();
  	}
    print_var(cur);
    if (scanf("%d", &cur) == EOF){
      invalid_cnf();
    }
  	while (cur != 0) {
  	  printf(" || ");
      print_var(cur);
      if (scanf("%d", &cur) == EOF) {
      	invalid_cnf();
      }
  	} 
  	printf(")");
  	if (i < num_clauses - 1){
  	  printf(" &&");	
  	}
  	putchar('\n');
  }
  return EXIT_SUCCESS;
}
