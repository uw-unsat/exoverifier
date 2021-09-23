#include <stdlib.h>
#include <stdio.h>
#include <assert.h>

void generate_selection_sort (int size){
  int i = 0;
  int j = 0;
  int k = 0;
  for (i = 0; i < size - 1; i++){
    printf("(min_%d_%d == a%d_%d) && ", i, i, i, i);
    printf("(minat_%d_%d == %d) &&\n", i, i , i);
    for (j = i+1; j < size; j++){
      printf("((min_%d_%d > a%d_%d) ?\n", i, j - 1, j, i);
      printf(" (min_%d_%d == a%d_%d) &&", i, j, j, i); 
      printf(" (minat_%d_%d == %d) :\n", i, j, j);
      printf(" (min_%d_%d == min_%d_%d) &&", i, j, i, j - 1);
      printf(" (minat_%d_%d == minat_%d_%d)) &&\n", i, j, i, j - 1);
    }
    if (i > 0){
      printf(" /* already processed elements do not change */\n");
    }
    for (k = 0; k < i; k++){
      printf(" (a%d_%d == a%d_%d) &&\n",k, i, k, i+1); 
    }
    printf(" /* swap */\n");
    printf(" (a%d_%d == min_%d_%d) &&\n", i, i+1, i, j - 1); 
    for (k = i+1; k < size; k++){
      printf(" ((minat_%d_%d == %d) ?\n", i, j - 1, k); 
      printf(" (a%d_%d == a%d_%d) :\n", k, i+1, i, i);
      printf(" (a%d_%d == a%d_%d))",k, i, k, i+1); 
      if (k < size - 1) {
        printf(" &&\n");
      }
    }
    if (i < size - 2){
      printf(" && \n");
    } else {
      printf("\n");
    }
  }
}

int main (int argc, char **argv){
  int size = 0;
  int i = 0;
  int j = 0;
  if (argc != 2){
    printf("Usage: selection_sort_c32sat_gen <size>\n");
    return 1;
  }
  size = atoi (argv[1]);
  if (size <= 1){
    printf("Size has to > 1\n");
    return 1;
  }
  printf("(");
  generate_selection_sort (size);
  printf(") => \n");
  printf("/* array is sorted */\n");
  for (i = 1; i < size; i++){
    printf ("(a%d_%d <= a%d_%d)", i - 1, size - 1, i, size - 1);
    if (i  < size - 1){
      printf(" && ");
    } else {
      printf("\n");
    }
  } 
  printf("/* Every element of the old array occurs also in the sorted array */\n");
  for (i = 0; i < size; i++){
    printf(" && ");
    printf("(");
    for (j = 0; j < size; j++){
      printf("(a%d_0 == a%d_%d)", i, j, size -1);
      if (j < size -1){
        printf(" || ");
      } else {
        printf(")\n");
      }
    }
  } 
  return 0;
}
