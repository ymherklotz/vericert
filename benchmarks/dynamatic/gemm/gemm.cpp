#include "gemm.h"
/**
 * gemver.c: This file is part of the PolyBench/C 3.2 test suite.
 *
 *
 * Contact: Louis-Noel Pouchet <pouchet@cse.ohio-state.edu>
 * Web address: http://polybench.sourceforge.net
 */


#include <stdlib.h>


#define N 4000


int gemm(in_float_t alpha, in_float_t beta, in_float_t A[30][30], in_float_t B[30][30], inout_float_t C[30][30] )
{
  int i, j, k;

 for (i = 0; i < 20; i++)
    for (j = 0; j < 20; j++)
      {
      	float tmp = C[i][j] *beta;
				for (k = 0; k < 20; ++k)
				    tmp += alpha * A[i][k] * B[k][j];

				C[i][j] = tmp;
      }
      return j;
}


#define AMOUNT_OF_TEST 1

int main(void){
	  in_float_t alpha[AMOUNT_OF_TEST];
	  in_float_t beta[AMOUNT_OF_TEST];
	  in_float_t A[AMOUNT_OF_TEST][30][30];
	  in_float_t B[AMOUNT_OF_TEST][30][30];
	  out_float_t C[AMOUNT_OF_TEST][30][30];
    
	for(int i = 0; i < AMOUNT_OF_TEST; ++i){
    alpha[i] = 1;
    beta[i] = 1;
    	for(int y = 0; y < 30; ++y){
    	    for(int x = 0; x < 30; ++x){
			      A[i][y][x] = rand()%2;
			      B[i][y][x] = rand()%3;
			      C[i][y][x] = 1;

          }
		  }
	}

	int i = 0; 
	gemm(alpha[i], beta[i], A[i], B[i], C[i]);
}




