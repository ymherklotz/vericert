#include "bicg.h"

//SEPARATOR_FOR_MAIN

#include <stdlib.h>

#include <stdio.h>
#include <unistd.h>
#include <string.h>
#include <math.h>


#define AMOUNT_OF_TEST 1

int bicg(in_float_t A[N][N], inout_float_t s[N], inout_float_t q[N], in_float_t p[N], in_float_t r[N]) {
  int j;
  int i = 0;

  float tmp_q = 0;

  for (i = 0; i < 30; i++) {
    tmp_q = q[i];
    for (j = 0; j < 30; j++) {
      float tmp =  A[i][j];
      s[j] = s[j] + r[i] * tmp;
      tmp_q = tmp_q + tmp * p[j];
    }
    q[i] = tmp_q;
  }

  return i; 
}

int main() {
  in_float_t A[AMOUNT_OF_TEST][N][N];
  inout_float_t s[AMOUNT_OF_TEST][N];
  inout_float_t q[AMOUNT_OF_TEST][N];
  in_float_t p[AMOUNT_OF_TEST][N];
  in_float_t r[AMOUNT_OF_TEST][N];

  for(int i = 0; i < AMOUNT_OF_TEST; ++i){
    for(int y = 0; y < N; ++y){
      s[i][y] = (rand()%100) + 1;
      q[i][y] = (rand()%100) + 1; 
      p[i][y] = (rand()%100) + 1; 
      r[i][y] = (rand()%100) + 1;
      for(int x = 0; x < N; ++x){
        A[i][y][x] = (rand()%100) + 1;
      }
    }
  }

  int i = 0;
  bicg(A[i], s[i], q[i], p[i], r[i]);
}