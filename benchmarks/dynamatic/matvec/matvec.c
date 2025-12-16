#include "matvec.h"
//------------------------------------------------------------------------
// MatVec
//------------------------------------------------------------------------

#define AMOUNT_OF_TEST 1

int matvec (in_int_t M[NM][NM], in_int_t V[NM], out_int_t Out[NM]) {
	int i, j;
	int tmp = 0;

	for (i=0;i<NM;i++) {
		tmp = 0;

		for (j=0;j<NM;j++) {
			tmp += V[j]* M[i][j];
		}
		Out[i] = tmp;
	}

	return i;

}

int main(void){
	in_int_t M[AMOUNT_OF_TEST][NM][NM];
	in_int_t V[AMOUNT_OF_TEST][NM];
	out_int_t Out[AMOUNT_OF_TEST][NM];
    
	for(int i = 0; i < AMOUNT_OF_TEST; ++i){
    	for(int y = 0; y < NM; ++y){
      		V[i][y] = y;
      		for(int x = 0; x < NM; ++x){
      			M[i][y][x] = x;
      		}
    	}
  	}

  	int i = 0;
	matvec(M[i], V[i], Out[i]);
}
