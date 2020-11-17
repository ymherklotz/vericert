/**
 * This version is stamped on May 10, 2016
 *
 * Contact:
 *   Louis-Noel Pouchet <pouchet.ohio-state.edu>
 *   Tomofumi Yuki <tomofumi.yuki.fr>
 *
 * Web address: http://polybench.sourceforge.net
 */
/* trisolv.c: this file is part of PolyBench/C */

#include "../../include/misc.h"


#ifndef SYNTHESIS
#include <stdio.h>
#endif 

#define plus(i) i = i + ONE
static
void init_array(int n,
  int L[ 40 ][40 ],
  int x[ 40 ],
  int b[ 40 ])
{
  int i, j;
  int ONE = 1;

  for (i = 0; i < n; plus(i))
    {
      x[i] = -999;
      b[i] = i ;
      for (j = 0; j <= i; plus(j))
        L[i][j] = (int) divider((i+n-j+ONE)*(ONE+ONE), n);
    }
}




static
int check_array(int n,
   int x[ 40])

{
  int i;
  int res = 0;
  int ONE = 1;
  for (i = 0; i < n; plus(i)) {
    res ^= x[i];
  }

#ifndef SYNTHESIS
    printf("finished: %u\n", res);
#endif
  return res;
}




static
void kernel_trisolv(int n,
      int L[ 40 + 0][40 + 0],
      int x[ 40 + 0],
      int b[ 40 + 0])
{
  int i, j;
  int ONE = 1;

  for (i = 0; i < n; plus(i))
  {
    x[i] = b[i];
    for (j = 0; j <i; plus(j))
      x[i] -= L[i][j] * x[j];

    x[i] = divider(x[i],L[i][i]);

  }

}


int main()
{

  int n = 40;


  int L[40 + 0][40 + 0]; 
  int x[40 + 0]; 
  int b[40 + 0]; 

  init_array (n, L, x, b);
  kernel_trisolv (n, L, x, b);

  return check_array(n, x);

  return 0;
}
