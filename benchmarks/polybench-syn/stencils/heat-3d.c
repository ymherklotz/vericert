/**
 * This version is stamped on May 10, 2016
 *
 * Contact:
 *   Louis-Noel Pouchet <pouchet.ohio-state.edu>
 *   Tomofumi Yuki <tomofumi.yuki.fr>
 *
 * Web address: http://polybench.sourceforge.net
 */
/* heat-3d.c: this file is part of PolyBench/C */

#include "../include/misc.h"

#ifndef SYNTHESIS
#include <stdio.h>
#endif

#define plus(i) i = i + ONE
static
void init_array (int n,
   int A[ 10 + 0][10 + 0][10 + 0],
   int B[ 10 + 0][10 + 0][10 + 0])
{
  int i, j, k;
  int ONE = 1;

  for (i = 0; i < n; plus(i))
    for (j = 0; j < n; plus(j))
      for (k = 0; k < n; plus(k))
        A[i][j][k] = B[i][j][k] = (int) (i + j + (n-k))* sdivider(10, n);
}




static
int print_array(int n,
   int A[ 10 + 0][10 + 0][10 + 0])

{
  int i, j, k;
  int ONE = 1;
  int res = 0;

  for (i = 0; i < n; plus(i))
    for (j = 0; j < n; plus(j))
      for (k = 0; k < n; plus(k)) {
         res ^= A[i][j][k];
      }
#ifndef SYNTHESIS
  printf("finished %u\n", res);
#endif
    return res;
}




static
void kernel_heat_3d(int tsteps,
        int n,
        int A[ 10 + 0][10 + 0][10 + 0],
        int B[ 10 + 0][10 + 0][10 + 0])
{
  int t, i, j, k;
  int ONE = 1;
  int TWO = 2;

 for (t = 1; t <= 5; plus(t)) {
        for (i = 1; i < n-ONE; plus(i)) {
            for (j = 1; j < n-ONE; plus(j)) {
                for (k = 1; k < n-ONE; plus(k)) {
                    B[i][j][k] = ((A[i+ONE][j][k] - TWO * A[i][j][k] + A[i-ONE][j][k]) >> 4) 
                                 + ((A[i][j+ONE][k] - TWO * A[i][j][k] + A[i][j-ONE][k]) >> 4)
                                 + ((A[i][j][k+ONE] - TWO * A[i][j][k] + A[i][j][k-ONE]) >> 4)
                                 + A[i][j][k]
                                    ;
                }
            }
        }
        for (i = 1; i < n-ONE; plus(i)) {
           for (j = 1; j < n-ONE; plus(j)) {
               for (k = 1; k < n-ONE; plus(k)) {
                   A[i][j][k] = ((B[i+ONE][j][k] - TWO * B[i][j][k] + B[i-ONE][j][k]) >> 4 )
                                + ((B[i][j+ONE][k] - TWO * B[i][j][k] + B[i][j-ONE][k]) >> 4 )
                                + ((B[i][j][k+ONE] - TWO * B[i][j][k] + B[i][j][k-ONE]) >> 4 )
                                + B[i][j][k];
                                    //;
               }
           }
       }
    }
}


int main()
{

  int n = 10;
  int tsteps = 20;


  int A[10 + 0][10 + 0][10 + 0];
  int B[10 + 0][10 + 0][10 + 0];

  init_array (n, A, B);

  kernel_heat_3d (tsteps, n, A, B);

  return print_array(n, A);

}
