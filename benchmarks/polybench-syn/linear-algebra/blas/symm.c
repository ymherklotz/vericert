/**
 * This version is stamped on May 10, 2016
 *
 * Contact:
 *   Louis-Noel Pouchet <pouchet.ohio-state.edu>
 *   Tomofumi Yuki <tomofumi.yuki.fr>
 *
 * Web address: http://polybench.sourceforge.net
 */
/* symm.c: this file is part of PolyBench/C */

#include "../../include/misc.h"

#ifndef SYNTHESIS
  #include <stdio.h>
#endif
#define plus(i) i = i + ONE
static
void init_array(int m, int n,
  int *alpha,
  int *beta,
  int C[ 20 + 0][30 + 0],
  int A[ 20 + 0][20 + 0],
  int B[ 20 + 0][30 + 0])
{
  int i, j;
  int ONE = 1;
  int HUND = 100;

  *alpha = 3;
  *beta = 2;
  for (i = 0; i < m; plus(i))
    for (j = 0; j < n; plus(j)) {
      C[i][j] = (int) divider(smodulo(i+j, HUND), m);
      B[i][j] = (int) divider(smodulo(n+i-j, HUND), m);
    }
  for (i = 0; i < m; plus(i)) {
    for (j = 0; j <=i; plus(j))
      A[i][j] = (int) divider(smodulo(i+j, HUND), m);
    for (j = i+ONE; j < m; plus(j))
      A[i][j] = -999;
  }
}

static
int print_array(int m, int n,
   int C[ 20 + 0][30 + 0])
{
  int i, j;
  int ONE = 1;
  int res = 0;

  for (i = 0; i < m; plus(i))
    for (j = 0; j < n; plus(j)) {
  res ^= C[i][j];
    }
#ifndef SYNTHESIS
  printf("finished %u\n", res);
#endif
    return res;
}


static
void kernel_symm(int m, int n,
   int alpha,
   int beta,
   int C[ 20 + 0][30 + 0],
   int A[ 20 + 0][20 + 0],
   int B[ 20 + 0][30 + 0])
{
  int ONE = 1;
  int i, j, k;
  int temp2;
 for (i = 0; i < m; plus(i))
      for (j = 0; j < n; plus(j) )
      {
        temp2 = 0;
        for (k = 0; k < i; plus(k)) {
           C[k][j] += alpha*B[i][j] * A[i][k];
           temp2 += B[k][j] * A[i][k];
        }
        C[i][j] = beta * C[i][j] + alpha*B[i][j] * A[i][i] + alpha * temp2;
     }

}


int main()
{

  int m = 20;
  int n = 30;

  int alpha;
  int beta;
  int C[20 + 0][30 + 0]; 
  int A[20 + 0][20 + 0]; 
  int B[20 + 0][30 + 0]; 


  init_array (m, n, &alpha, &beta,
       C,
       A,
       B);

  kernel_symm (m, n,
        alpha, beta,
        C,
        A,
        B);

 return 
  print_array(m, n, C);

}
