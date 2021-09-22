/**
 * This version is stamped on May 10, 2016
 *
 * Contact:
 *   Louis-Noel Pouchet <pouchet.ohio-state.edu>
 *   Tomofumi Yuki <tomofumi.yuki.fr>
 *
 * Web address: http://polybench.sourceforge.net
 */
/* jacobi-2d.c: this file is part of PolyBench/C */

#include "../include/misc.h"

#ifndef SYNTHESIS
#include <stdio.h>
#endif


#define plus(i) i = i + ONE
static
void init_array (int n,
   int A[ 30 + 0][30 + 0],
   int B[ 30 + 0][30 + 0])
{
  int i, j;
  int ONE = 1;
  int TWO = 2;
  int THREE = 3;

  for (i = 0; i < n; plus(i))
    for (j = 0; j < n; plus(j))
      {
        A[i][j] = (((int) i*(j+TWO) + TWO) / n);
        B[i][j] = (((int) i*(j+THREE) + THREE) / n);
      }
}




static
int print_array(int n,
   int A[ 30 + 0][30 + 0])

{
  int i, j;
  int ONE = 1;
  int res = 0;

  for (i = 0; i < n; plus(i))
    for (j = 0; j < n; plus(j)) {
      res ^= A[i][j];
    }
#ifndef SYNTHESIS
  printf("finished %u\n", res);
#endif
    return res;
}




static
void kernel_jacobi_2d(int tsteps,
       int n,
       int A[ 30 + 0][30 + 0],
       int B[ 30 + 0][30 + 0])
{
  int t, i, j;
  int ONE = 1;
  int TWO = 2;

  for (t = 0; t < tsteps; plus(t))
  {
    for (i = 1; i < n - ONE; plus(i))
      for (j = 1; j < n - ONE; plus(j)){
        B[i][j] = (A[i][j] + A[i][j-ONE] + A[i][ONE+j] + A[ONE+i][j] + A[i-ONE][j]);
        B[i][j] = B[i][j] >> TWO;
      }
    for (i = 1; i < n - ONE; plus(i))
      for (j = 1; j < n - ONE; plus(j)){
        A[i][j] = (B[i][j] + B[i][j-ONE] + B[i][ONE+j] + B[ONE+i][j] + B[i-ONE][j]);
        A[i][j] = A[i][j] >> TWO; 
      }
  }

}


int main()
{

  int n = 30;
  int tsteps = 5;


  int A[30 + 0][30 + 0];
  int B[30 + 0][30 + 0];



  init_array (n, A, B);

  kernel_jacobi_2d(tsteps, n, A, B);

  return print_array(n, A);

}
