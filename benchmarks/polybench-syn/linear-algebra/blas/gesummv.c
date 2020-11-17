/**
 * This version is stamped on May 10, 2016
 *
 * Contact:
 *   Louis-Noel Pouchet <pouchet.ohio-state.edu>
 *   Tomofumi Yuki <tomofumi.yuki.fr>
 *
 * Web address: http://polybench.sourceforge.net
 */
/* gesummv.c: this file is part of PolyBench/C */

#include "../../include/misc.h"
#ifndef SYNTHESIS
    #include <stdio.h>
#endif

#define plus(i) i = i + ONE

  static
void init_array(int n,
    int *alpha,
    int *beta,
    int A[ 30 + 0][30 + 0],
    int B[ 30 + 0][30 + 0],
    int x[ 30 + 0])
{
  int i, j;
  int ONE = 1;

  *alpha = 3;
  *beta = 2;
  for (i = 0; i < n; plus(i))
  {
    x[i] = (int) divider(smodulo(i, n), n);
    for (j = 0; j < n; plus(j)) {
      A[i][j] = (int) divider(smodulo(i*j+ONE, n), n);
      B[i][j] = (int) divider(smodulo(i*j+ONE+ONE, n), n);
    }
  }
}


  static
int print_array(int n,
    int y[ 30 + 0])

{
  int i;
  int ONE = 1;
  int res = 0;

  for (i = 0; i < n; plus(i)) {
    res ^= y[i];
  }
#ifndef SYNTHESIS
    printf("finished: %u\n", res);
#endif
  return res;
}

  static
void kernel_gesummv(int n,
    int alpha,
    int beta,
    int A[ 30 + 0][30 + 0],
    int B[ 30 + 0][30 + 0],
    int tmp[ 30 + 0],
    int x[ 30 + 0],
    int y[ 30 + 0])
{
  int i, j;
  int ONE = 1;

  for (i = 0; i < n; plus(i))
  {
    tmp[i] = 0;
    y[i] = 0;
    for (j = 0; j < n; plus(j))
    {
      tmp[i] = A[i][j] * x[j] + tmp[i];
      y[i] = B[i][j] * x[j] + y[i];
    }
    y[i] = alpha * tmp[i] + beta * y[i];
  }
}


int main()
{

  int n = 30;


  int alpha;
  int beta;
  int A[30 + 0][30 + 0]; 
  int B[30 + 0][30 + 0]; 
  int tmp[30 + 0];  
  int x[30 + 0]; 
  int y[30 + 0]; 

  init_array (n, &alpha, &beta,
      A,
      B,
      x);

  kernel_gesummv (n, alpha, beta,
      A,
      B,
      tmp,
      x,
      y);


  return print_array(n, y);

}
