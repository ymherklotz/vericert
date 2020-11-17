/**
 * This version is stamped on May 10, 2016
 *
 * Contact:
 *   Louis-Noel Pouchet <pouchet.ohio-state.edu>
 *   Tomofumi Yuki <tomofumi.yuki.fr>
 *
 * Web address: http://polybench.sourceforge.net
 */
/* jacobi-1d.c: this file is part of PolyBench/C */

#include "../include/misc.h"

#ifndef SYNTHESIS
#include <stdio.h>
#endif

#define plus(i) i = i + ONE
static
void init_array (int n,
   int A[ 30 + 0],
   int B[ 30 + 0])
{
  int i;
  int ONE = 1;
  int TWO = 2;
  int THREE = 3;

  for (i = 0; i < n; plus(i))
      {
        A[i] = divider(((int) i+TWO), n);
        B[i] = divider(((int) i+THREE), n);
      }
}




static
int print_array(int n,
   int A[ 30 + 0])

{
  int i;
  int ONE = 1;
  int res = 0;

  for (i = 0; i < n; plus(i))
    {
      res ^= A[i];
    }
#ifndef SYNTHESIS
  printf("finished %u\n", res);
#endif
    return res;
}




static
void kernel_jacobi_1d(int tsteps,
       int n,
       int A[ 30 + 0],
       int B[ 30 + 0])
{
  int t, i;
  int ONE = 1;

  for (t = 0; t < tsteps; plus(t))
  {
    for (i = 1; i < n - ONE; plus(i)){
      B[i] = (A[i-ONE] + A[i] + A[i + ONE]);
      B[i] = B[i] >> 2;
    }
    for (i = 1; i < n - ONE; plus(i)){
      A[i] = (B[i-ONE] + B[i] + B[i + ONE]);
      A[i] = A[i] >> 2;
    }
  }

}


int main()
{

  int n = 30;
  int tsteps = 20;


  int A[30 + 0]; 
  int B[30 + 0]; 



  init_array (n, A, B);

  kernel_jacobi_1d(tsteps, n, A, B);

  return print_array(n, A);

}
