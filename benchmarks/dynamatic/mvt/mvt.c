#include "mvt.h"
/**
 * This file is part of the PolyBench/C 3.2 test suite.
 *
 *
 * Contact: Louis-Noel Pouchet <pouchet@cse.ohio-state.edu>
 * Web address: http://polybench.sourceforge.net
 */


#include <stdlib.h>


int mvt(int A[30][30], int x1[30], int x2[30], int y1[30], int y2[30])
{
   for (int i = 0; i < 30; i++) {
   	int tmp = x1[i];
    for (int j = 0; j < 30; j++)
      tmp = tmp + A[i][j] * y1[j];
    x1[i] = tmp;
	}

	int m;
  for (m = 0; m < 30; m++) {
  	int tmp = x2[m];
    for (int n = 0; n < 30; n++)
      tmp = tmp + A[n][m] * y2[n];
  	x2[m] = tmp;
	}

	return m;
}



#define AMOUNT_OF_TEST 1

int main(void){

	  int A[AMOUNT_OF_TEST][30][30];
	  int x1[AMOUNT_OF_TEST][30];
	  int x2[AMOUNT_OF_TEST][30];
	  int y1[AMOUNT_OF_TEST][30];
	  int y2[AMOUNT_OF_TEST][30];

    
	for(int i = 0; i < AMOUNT_OF_TEST; ++i){
    	for(int y = 0; y < 30; ++y){
    		x1[i][y] = y&1 == 1;
    		x2[i][y] = y&1 == 1;
    		y1[i][y] = y&1 == 1;
    		y2[i][y] = y&1 == 1;
    	    for(int x = 0; x < 30; ++x){
			      A[i][y][x] = y&1 == 1;
          	}
		 }
	}

	int i = 0; 
    mvt(A[i], x1[i], x2[i], y1[i], y2[i]);
	return x2[i][4];
}
