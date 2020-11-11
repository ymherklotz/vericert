/**
 * This version is stamped on May 10, 2016
 *
 * Contact:
 *   Louis-Noel Pouchet <pouchet.ohio-state.edu>
 *   Tomofumi Yuki <tomofumi.yuki.fr>
 *
 * Web address: http://polybench.sourceforge.net
 */
/* 3mm.c: this file is part of PolyBench/C */


#include "../../include/misc.h"

#define plus(i) i = i + ONE
static
void init_array(int ni, int nj, int nk, int nl, int nm,
  int A[ 16 + 0][20 + 0],
  int B[ 20 + 0][18 + 0],
  int C[ 18 + 0][24 + 0],
  int D[ 24 + 0][22 + 0])
{
  int i, j;
  int ONE = 1;
  int TWO = 2;
  int THREE = 3;

  for (i = 0; i < ni; plus(i))
    for (j = 0; j < nk; plus(j))
      A[i][j] = (int) divider(smodulo((i*j+ONE), ni), (5*ni));
  for (i = 0; i < nk; plus(i))
    for (j = 0; j < nj; plus(j))
      B[i][j] = (int) divider(smodulo((i*(j+ONE)+TWO),nj), (5*nj));
  for (i = 0; i < nj; plus(i))
    for (j = 0; j < nm; plus(j))
      C[i][j] = (int) divider(smodulo(i*(j+THREE), nl), (5*nl));
  for (i = 0; i < nm; plus(i))
    for (j = 0; j < nl; plus(j))
      D[i][j] = (int) divider(smodulo((i*(j+TWO)+TWO), nk), (5*nk));
}


static
int print_array(int ni, int nl,
   int G[ 16 + 0][22 + 0])
{
  int i, j;
  int ONE = 1;
  int res = 0;

  for (i = 0; i < ni; plus(i))
    for (j = 0; j < nl; plus(j)) {
      res ^= G[i][j];
    }
    return res;
}




static
void kernel_3mm(int ni, int nj, int nk, int nl, int nm,
  int E[ 16 + 0][18 + 0],
  int A[ 16 + 0][20 + 0],
  int B[ 20 + 0][18 + 0],
  int F[ 18 + 0][22 + 0],
  int C[ 18 + 0][24 + 0],
  int D[ 24 + 0][22 + 0],
  int G[ 16 + 0][22 + 0])
{
  int ONE = 1;
  int i, j, k;

 for (i = 0; i < ni; plus(i))
    for (j = 0; j < nj; plus(j))
      {
 E[i][j] = 0;
 for (k = 0; k < nk; plus(k))
   E[i][j] += A[i][k] * B[k][j];
      }

  for (i = 0; i < nj; plus(i))
    for (j = 0; j < nl; plus(j))
      {
 F[i][j] = 0;
 for (k = 0; k < nm; plus(k))
   F[i][j] += C[i][k] * D[k][j];
      }

  for (i = 0; i < ni; plus(i))
    for (j = 0; j < nl; plus(j))
      {
 G[i][j] = 0;
 for (k = 0; k < nj; plus(k))
   G[i][j] += E[i][k] * F[k][j];
      }

}

int main()
{

  int ni = 16;
  int nj = 18;
  int nk = 20;
  int nl = 22;
  int nm = 24;


  int E[16 + 0][18 + 0]; 
  int A[16 + 0][20 + 0]; 
  int B[20 + 0][18 + 0]; 
  int F[18 + 0][22 + 0]; 
  int C[18 + 0][24 + 0]; 
  int D[24 + 0][22 + 0]; 
  int G[16 + 0][22 + 0]; 


  init_array (ni, nj, nk, nl, nm,
       A,
       B,
       C,
       D);

  kernel_3mm (ni, nj, nk, nl, nm,
       E,
       A,
       B,
       F,
       C,
       D,
       G);


  return print_array(ni, nl, G);

}
