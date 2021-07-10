/**
 * This version is stamped on May 10, 2016
 *
 * Contact:
 *   Louis-Noel Pouchet <pouchet.ohio-state.edu>
 *   Tomofumi Yuki <tomofumi.yuki.fr>
 *
 * Web address: http://polybench.sourceforge.net
 */
/* seidel-2d.c: this file is part of PolyBench/C */

#include "../include/misc.h"

#ifndef SYNTHESIS
#include <stdio.h>
#endif

#define plus(i) i = i + ONE
static
void init_array (int n,
   int A[ 40 + 0][40 + 0])
{
  int i, j;
  int ONE = 1;
  int TWO = 2;

  for (i = 0; i < n; plus(i))
    for (j = 0; j < n; plus(j))
      A[i][j] = (((int) i*(j+TWO) + TWO) / n);
}




static
int print_array(int n,
   int A[ 40 + 0][40 + 0])

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
void kernel_seidel_2d(int tsteps,
        int n,
        int A[ 40 + 0][40 + 0])
{
  int t, i, j;
  int ONE = 1;
  int TWO = 2;
  int NINE = 9;

 for (t = 0; t <= tsteps - ONE; plus(t))
    for (i = ONE; i<= n - TWO; plus(i))
      for (j = ONE; j <= n - TWO; plus(j))
 A[i][j] = ((A[i-ONE][j-ONE] + A[i-ONE][j] + A[i-ONE][j+ONE]
     + A[i][j-ONE] + A[i][j] + A[i][j+ONE]
     + A[i+ONE][j-ONE] + A[i+ONE][j] + A[i+ONE][j+ONE]) / NINE);

}


int main()
{

  int n = 40;
  int tsteps = 5;


  int A[40 + 0][40 + 0]; 

  init_array (n, A);

  kernel_seidel_2d (tsteps, n, A);

  return print_array(n, A);

}
