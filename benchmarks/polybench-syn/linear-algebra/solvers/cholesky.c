/**
 * This version is stamped on May 10, 2016
 *
 * Contact:
 *   Louis-Noel Pouchet <pouchet.ohio-state.edu>
 *   Tomofumi Yuki <tomofumi.yuki.fr>
 *
 * Web address: http://polybench.sourceforge.net
 */
/* cholesky.c: this file is part of PolyBench/C */

#include "../../include/misc.h"

#  define SQRT_FUN(x) sqrtf(x)

#define plus(i) i = i + ONE
static
void init_array(int n,
  int A[40][40])
{
  int i, j;
  int ONE = 1;

  for (i = 0; i < n; plus(i))
    {
      for (j = 0; j <= i; plus(j))
 A[i][j] = (int)sdivider(smodulo(-j, n), n) + ONE;
      for (j = i + ONE; j < n; plus(j)) {
 A[i][j] = 0;
      }
      A[i][i] = 1;
    }


  int r,s,t;
  int B[40][40]; 
  for (r = 0; r < n; ++r)
    for (s = 0; s < n; ++s)
      B[r][s] = 0;
  for (t = 0; t < n; ++t)
    for (r = 0; r < n; ++r)
      for (s = 0; s < n; ++s)
 B[r][s] += A[r][t] * A[s][t];
    for (r = 0; r < n; ++r)
      for (s = 0; s < n; ++s)
 A[r][s] = B[r][s];

}




static
int check_array(int n,
   int A[40][40])

{
  int res = 0;
  int ONE = 1;
  int i, j;

  for (i = 0; i < n; plus(i))
    for (j = 0; j <= i; plus(j)) {
    if(A[i][j]!=0) res = 1;
  }
  return res;
}




static
void kernel_cholesky(int n,
       int A[40][40])
{
  int i, j, k;
  int ONE = 1;

  for (i = 0; i < n; plus(i)) {

    for (j = 0; j < i; plus(j)) {
      for (k = 0; k < j; plus(k)) {
        A[i][j] -= A[i][k] * A[j][k];
      }
      A[i][j] = sdivider(A[i][j] ,A[j][j]);
    }

    for (k = 0; k < i; plus(k)) {
      A[i][i] -= A[i][k] * A[i][k];
    }
    int sq = 0; int val = 0; int cmp = A[i][i];
    while(sq <= cmp) {
      val = val + ONE;
      sq = val * val;
    }
    A[i][i] = val;
  }

}


int main()
{

  int n = 40;


  int A[40][40]; 


  init_array (n, A);


  kernel_cholesky (n, A);


  return check_array(n, A);


  return 0;
}
