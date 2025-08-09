#include "bicg.h"

//SEPARATOR_FOR_MAIN

#include <stdlib.h>

#include <stdio.h>
#include <unistd.h>
#include <string.h>
#include <math.h>


#define AMOUNT_OF_TEST 1

int bicg(int A[N][N], int s[N], int q[N], int p[N], int r[N]) {
  int j;
  int i = 0;

  int tmp_q = 0;

  for (i = 0; i < 30; i++) {
    tmp_q = q[i];
    for (j = 0; j < 30; j++) {
      int tmp =  A[i][j];
      s[j] = s[j] + r[i] * tmp;
      tmp_q = tmp_q + tmp * p[j];
    }
    q[i] = tmp_q;
  }

  return i; 
}

int main() {
  int A[AMOUNT_OF_TEST][N][N];
  int s[AMOUNT_OF_TEST][N];
  int q[AMOUNT_OF_TEST][N];
  int p[AMOUNT_OF_TEST][N];
  int r[AMOUNT_OF_TEST][N];

  for(int i = 0; i < AMOUNT_OF_TEST; ++i){
    for(int y = 0; y < N; ++y){
      s[i][y] = (y) + 1;
      q[i][y] = (y+1) + 1; 
      p[i][y] = (y+2) + 1; 
      r[i][y] = (y+3) + 1;
      for(int x = 0; x < N; ++x){
        A[i][y][x] = (x+y) + 1;
      }
    }
  }

  int i = 0;
  bicg(A[i], s[i], q[i], p[i], r[i]);
}
