/**
 * This version is stamped on May 10, 2016
 *
 * Contact:
 *   Louis-Noel Pouchet <pouchet.ohio-state.edu>
 *   Tomofumi Yuki <tomofumi.yuki.fr>
 *
 * Web address: http://polybench.sourceforge.net
 */
/* bicg.c: this file is part of PolyBench/C */


#include "../../include/misc.h"

#ifndef SYNTHESIS
 #include <stdio.h> 
#endif

#define plus(i) i = i + ONE
static
void init_array (int m, int n,
   int A[ 42 + 0][38 + 0],
   int r[ 42 + 0],
   int p[ 38 + 0])
{
  int i, j;
  int ONE = 1;

  for (i = 0; i < m; plus(i))
    p[i] = divider(smodulo(i, m), m);
  for (i = 0; i < n; plus(i)) {
    r[i] = divider(smodulo(i, n), n);
    for (j = 0; j < m; plus(j))
      A[i][j] = divider(smodulo(i*(j+ONE), n), n);
  }
}




static
int print_array(int m, int n,
   int s[ 38 + 0],
   int q[ 42 + 0])

{
  int i;
  int ONE = 1;
  int res = 0;

  for (i = 0; i < m; plus(i)) {
    res ^= s[i];
  }
  for (i = 0; i < n; plus(i)) {
    res ^= q[i];
  }
#ifndef SYNTHESIS
  printf("finished %u\n", res);
#endif
  return res;
}




static
void kernel_bicg(int m, int n,
   int A[ 42 + 0][38 + 0],
   int s[ 38 + 0],
   int q[ 42 + 0],
   int p[ 38 + 0],
   int r[ 42 + 0])
{
  int i, j;
  int ONE = 1;

 for (i = 0; i < m; plus(i))
    s[i] = 0;
  for (i = 0; i < n; plus(i))
    {
      q[i] = 0;
      for (j = 0; j < m; plus(j))
 {
   s[j] = s[j] + r[i] * A[i][j];
   q[i] = q[i] + A[i][j] * p[j];
 }
    }

}


int main()
{

  int n = 42;
  int m = 38;


  int A[42 + 0][38 + 0]; 
  int s[38 + 0]; 
  int q[42 + 0]; 
  int p[38 + 0]; 
  int r[42 + 0]; 


  init_array (m, n,
       A,
       r,
       p);

  kernel_bicg (m, n,
        A,
        s,
        q,
        p,
        r);


  return print_array(m, n, s, q);


}
