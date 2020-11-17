/**
 * This version is stamped on May 10, 2016
 *
 * Contact:
 *   Louis-Noel Pouchet <pouchet.ohio-state.edu>
 *   Tomofumi Yuki <tomofumi.yuki.fr>
 *
 * Web address: http://polybench.sourceforge.net
 */
/* gemver.c: this file is part of PolyBench/C */

#include "../../include/misc.h"

#ifndef SYNTHESIS
  #include <stdio.h>
#endif
#define plus(i) i = i + ONE
static
void init_array (int n,
   int *alpha,
   int *beta,
   int A[ 40 + 0][40 + 0],
   int u1[ 40 + 0],
   int v1[ 40 + 0],
   int u2[ 40 + 0],
   int v2[ 40 + 0],
   int w[ 40 + 0],
   int x[ 40 + 0],
   int y[ 40 + 0],
   int z[ 40 + 0])
{
  int i, j;
  int ONE = 1;

  *alpha = 3;
  *beta = 2;

  int fn = (int)n;

  for (i = 0; i < n; plus(i))
    {
      u1[i] = i;
      u2[i] = divider((i+ONE),fn*2);
      v1[i] = divider((i+ONE),fn*4);
      v2[i] = divider((i+ONE),fn*6);
      y[i] =  divider((i+ONE),fn*8);
      z[i] =  divider((i+ONE),fn*9);
      x[i] = 0;
      w[i] = 0;
      for (j = 0; j < n; plus(j))
        A[i][j] = (int) divider(smodulo(i*j, n), n);
    }
}




static
int print_array(int n,
   int w[ 40 + 0])
{
  int i;
  int ONE = 1;
  int res = 0;

  for (i = 0; i < n; plus(i)) {
    res ^= w[i];
  }
#ifndef SYNTHESIS
  printf("finished %u\n", res);
#endif
  return res;
}




static
void kernel_gemver(int n,
     int alpha,
     int beta,
     int A[ 40 + 0][40 + 0],
     int u1[ 40 + 0],
     int v1[ 40 + 0],
     int u2[ 40 + 0],
     int v2[ 40 + 0],
     int w[ 40 + 0],
     int x[ 40 + 0],
     int y[ 40 + 0],
     int z[ 40 + 0])
{
  int i, j;
  int ONE = 1;

 for (i = 0; i < n; plus(i))
    for (j = 0; j < n; plus(j))
      A[i][j] = A[i][j] + u1[i] * v1[j] + u2[i] * v2[j];

  for (i = 0; i < n; plus(i))
    for (j = 0; j < n; plus(j))
      x[i] = x[i] + beta * A[j][i] * y[j];

  for (i = 0; i < n; plus(i))
    x[i] = x[i] + z[i];

  for (i = 0; i < n; plus(i))
    for (j = 0; j < n; plus(j))
      w[i] = w[i] + alpha * A[i][j] * x[j];

}


int main()
{

  int n = 40;


  int alpha;
  int beta;
  int A[40 + 0][40 + 0];  
  int u1[40 + 0]; 
  int v1[40 + 0]; 
  int u2[40 + 0]; 
  int v2[40 + 0]; 
  int w[40 + 0]; 
  int x[40 + 0]; 
  int y[40 + 0]; 
  int z[40 + 0]; 



  init_array (n, &alpha, &beta,
       A,
       u1,
       v1,
       u2,
       v2,
       w,
       x,
       y,
       z);

  kernel_gemver (n, alpha, beta,
   A,
   u1,
   v1,
   u2,
   v2,
   w,
   x,
   y,
   z);

  return print_array(n, w);

}
