
//------------------------------------------------------------------------
// Jianyi Cheng, DSS
// https://zenodo.org/record/3561115
//------------------------------------------------------------------------


#include <stdlib.h>
#include "gsum_many.h"

int gsum_many(int a[N], int c[N]) { 
	int i;
 	int d;
	int kk = 0;
	for(kk = 0; kk < 10; kk++) {
           int s= 0;
		for (i=0; i<1000; i++){
           d = a[i];
	       if (d >= 0) 
	      	s += (((((d+1)*d+1)*d+1)*d+1)*d);
    	}
    	c[kk] = s;
	}
	
	return kk;

}

#define AMOUNT_OF_TEST 1

int main(void){
	int a[AMOUNT_OF_TEST][N];

	int aya[AMOUNT_OF_TEST][N];

	int b[AMOUNT_OF_TEST][N];

    int c[AMOUNT_OF_TEST][N];

    
	for(int i = 0; i < AMOUNT_OF_TEST; ++i){
		for(int j = 0; j < N; ++j){
    		a[i][j] = 1 - j;
			b[i][j] = j + 10;

			c[i][j] = j + 10;
			aya[i][j] = 1 - j;

			if (j == 0)
			   	a[i][j] = j;
		}
	}

	int i = 0;
	gsum_many(a[i],c[i]);

}




