/**
 * This version is stamped on May 10, 2016
 *
 * Contact:
 *   Louis-Noel Pouchet <pouchet.ohio-state.edu>
 *   Tomofumi Yuki <tomofumi.yuki.fr>
 *
 * Web address: http://polybench.sourceforge.net
 */
/* trmm.c: this file is part of PolyBench/C */

#include "../../include/misc.h"

#ifndef SYNTHESIS
  #include <stdio.h>
#endif
#define plus(i) i = i + ONE
  static
void init_array(int m, int n,
    int *alpha,
    int A[ 20 + 0][20 + 0],
    int B[ 20 + 0][30 + 0])
{
  int i, j;
  int ONE = 1;

  *alpha = 3;
  for (i = 0; i < m; plus(i)) {
    for (j = 0; j < i; plus(j)) {
      A[i][j] = (int) divider(smodulo(i+j, m), m);
    }
    A[i][i] = 1;
    for (j = 0; j < n; plus(j)) {
      B[i][j] = (int)divider(smodulo(n+i-j, n), n);
    }
  }

}




  static
int print_array(int m, int n,
    int B[ 20 + 0][30 + 0])
{
  int i, j;
  int ONE = 1;
  int res = 0;

  for (i = 0; i < m; plus(i))
    for (j = 0; j < n; plus(j)) {
      res ^= B[i][j];
    }
#ifndef SYNTHESIS
  printf("finished %u\n", res);
#endif
  return res;
}




  static
void kernel_trmm(int m, int n,
    int alpha,
    int A[ 20 + 0][20 + 0],
    int B[ 20 + 0][30 + 0])
{
  int i, j, k;
  int ONE = 1;
  for (i = 0; i < m; plus(i))
    for (j = 0; j < n; plus(j)) {
      for (k = i+ONE; k < m; plus(k))
        B[i][j] += A[k][i] * B[k][j];
      B[i][j] = alpha * B[i][j];
    }

}


int main()
{

  int m = 20;
  int n = 30;


  int alpha;
  int A[20 + 0][20 + 0]; 
  int B[20 + 0][30 + 0]; 


  init_array (m, n, &alpha, A, B);


  kernel_trmm (m, n, alpha, A, B);

  return print_array(m, n, B);

}
