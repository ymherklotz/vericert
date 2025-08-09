#include "img_avg.h"


#include <stdlib.h>


int img_avg(in_int_t A[N], in_float_t B[N], inout_float_t C[N])
{
  int i;
	int thr;
	for(i = 0; i < N; i++ ) {
    	thr = A[i];
    	float s = 0.0;
    	if(thr > 0) {  
    		  for(int j = 0; j < 5; j++)
						s += B[j];
    	} else {
					s = B[0];	
    	}
    	C[i] = s * 2; 
	}

	return i;
}



#define AMOUNT_OF_TEST 1

int main(void){

	in_int_t thr[AMOUNT_OF_TEST][N];

	in_float_t b[AMOUNT_OF_TEST][N];

  inout_float_t c[AMOUNT_OF_TEST][N];

    for(int i = 0; i < AMOUNT_OF_TEST; ++i)
    for(int j = 0; j < N; ++j){
			b[i][j] = (float) j + 10;

			c[i][j] = (float) j + 10;
			thr[i][j] = j;

			if (j%10 == 0)
			   	thr[i][j] = 1-j;
		}

    int i = 0;
    img_avg(thr[i], b[i], c[i]);
}




