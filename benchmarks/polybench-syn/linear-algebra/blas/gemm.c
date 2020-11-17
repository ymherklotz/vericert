/**
 * This version is stamped on May 10, 2016
 *
 * Contact:
 *   Louis-Noel Pouchet <pouchet.ohio-state.edu>
 *   Tomofumi Yuki <tomofumi.yuki.fr>
 *
 * Web address: http://polybench.sourceforge.net
 */
/* gemm.c: this file is part of PolyBench/C */

#include "../../include/misc.h"

#ifndef SYNTHESIS
  #include <stdio.h>
#endif
#define plus(i) i = i + ONE
  static
void init_array(int ni, int nj, int nk,
    int *alpha,
    int *beta,
    int C[ 20 + 0][25 + 0],
    int A[ 20 + 0][30 + 0],
    int B[ 30 + 0][25 + 0])
{
  int i, j;
  int ONE = 1;

  *alpha = 2;
  *beta = 2;
  for (i = 0; i < ni; plus(i))
    for (j = 0; j < nj; plus(j))
      C[i][j] = (int) divider(smodulo(i*j+ONE, ni), ni);
  for (i = 0; i < ni; plus(i))
    for (j = 0; j < nk; plus(j))
      A[i][j] = (int) divider(smodulo(i*(j+ONE), nk), nk);
  for (i = 0; i < nk; plus(i))
    for (j = 0; j < nj; plus(j))
      B[i][j] = (int) divider(smodulo(i*(j+ONE+ONE), nj), nj);
}




  static
int print_array(int ni, int nj,
    int C[ 20 + 0][25 + 0])
{
  int i, j;
  int ONE = 1;
  int res = 0;
  for (i = 0; i < ni; plus(i))
    for (j = 0; j < nj; plus(j)) {
      res ^= C[i][j];
    }
#ifndef SYNTHESIS
  printf("finished %u\n", res);
#endif
  return res;
}

  static
void kernel_gemm(int ni, int nj, int nk,
    int alpha,
    int beta,
    int C[ 20 + 0][25 + 0],
    int A[ 20 + 0][30 + 0],
    int B[ 30 + 0][25 + 0])
{
  int i, j, k;
  int ONE = 1;

  for (i = 0; i < ni; plus(i)) {
    for (j = 0; j < nj; plus(j))
      C[i][j] *= beta;
    for (k = 0; k < nk; plus(k)) {
      for (j = 0; j < nj; plus(j))
        C[i][j] += alpha * A[i][k] * B[k][j];
    }
  }

}


int main()
{

  int ni = 20;
  int nj = 25;
  int nk = 30;


  int alpha;
  int beta;
  int C[20 + 0][25 + 0]; 
  int A[20 + 0][30 + 0]; 
  int B[30 + 0][25 + 0]; 


  init_array (ni, nj, nk, &alpha, &beta,
      C,
      A,
      B);


  kernel_gemm (ni, nj, nk,
      alpha, beta,
      C,
      A,
      B);


  return 
    print_array(ni, nj, C);


}
