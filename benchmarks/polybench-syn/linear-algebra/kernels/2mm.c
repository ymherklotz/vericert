/**
 * This version is stamped on May 10, 2016
 *
 * Contact:
 *   Louis-Noel Pouchet <pouchet.ohio-state.edu>
 *   Tomofumi Yuki <tomofumi.yuki.fr>
 *
 * Web address: http://polybench.sourceforge.net
 */
/* 2mm.c: this file is part of PolyBench/C */


#include "../../include/misc.h"

#ifndef SYNTHESIS
 #include <stdio.h> 
#endif

#define plus(i) i = i + ONE
static
void init_array(int ni, int nj, int nk, int nl,
  int *alpha,
  int *beta,
  int A[ 16 + 0][22 + 0],
  int B[ 22 + 0][18 + 0],
  int C[ 18 + 0][24 + 0],
  int D[ 16 + 0][24 + 0])
{
  int i, j;
  int ONE = 1;

  *alpha = 2;
  *beta = 2;
  for (i = 0; i < ni; plus(i))
    for (j = 0; j < nk; plus(j))
      A[i][j] = (int) divider(smodulo(i*j+ONE, ni), ni);
  for (i = 0; i < nk; plus(i))
    for (j = 0; j < nj; plus(j))
      B[i][j] = (int) divider(smodulo(i*(j+ONE), nj), nj);
  for (i = 0; i < nj; plus(i))
    for (j = 0; j < nl; plus(j))
      C[i][j] = (int) divider(smodulo(i*(j+ONE+ONE+ONE)+ONE, nl), nl);
  for (i = 0; i < ni; plus(i))
    for (j = 0; j < nl; plus(j))
      D[i][j] = (int) divider(smodulo(i*(j+ONE+ONE), nk), nk);
}

static
int print_array(int ni, int nl,
   int D[ 16 + 0][24 + 0])
{
  int i, j;
  int ONE = 1;
  int res = 0;
  for (i = 0; i < ni; plus(i))
    for (j = 0; j < nl; plus(j)) {
      res ^= D[i][j];
    }
#ifndef SYNTHESIS
  printf("finished %u\n", res);
#endif
  return res;
}




static
void kernel_2mm(int ni, int nj, int nk, int nl,
  int alpha,
  int beta,
  int tmp[ 16 + 0][18 + 0],
  int A[ 16 + 0][22 + 0],
  int B[ 22 + 0][18 + 0],
  int C[ 18 + 0][24 + 0],
  int D[ 16 + 0][24 + 0])
{
  int ONE = 1;
  int i, j, k;

 for (i = 0; i < ni; plus(i))
    for (j = 0; j < nj; plus(j))
      {
 tmp[i][j] = 0;
 for (k = 0; k < nk; plus(k))
   tmp[i][j] += alpha * A[i][k] * B[k][j];
      }
  for (i = 0; i < ni; plus(i))
    for (j = 0; j < nl; plus(j))
      {
 D[i][j] *= beta;
 for (k = 0; k < nj; plus(k))
   D[i][j] += tmp[i][k] * C[k][j];
      }

}


int main()
{

  int ni = 16;
  int nj = 18;
  int nk = 22;
  int nl = 24;

  int alpha;
  int beta;
  int tmp[16 + 0][18 + 0];
  int A[16 + 0][22 + 0];
  int B[22 + 0][18 + 0];
  int C[18 + 0][24 + 0];
  int D[16 + 0][24 + 0];


  init_array (ni, nj, nk, nl, &alpha, &beta,
       A,
       B,
       C,
       D);


  kernel_2mm (ni, nj, nk, nl,
       alpha, beta,
       tmp,
       A,
       B,
       C,
       D);


  return print_array(ni, nl, D);

}
