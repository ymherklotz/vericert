/**
 * This version is stamped on May 10, 2016
 *
 * Contact:
 *   Louis-Noel Pouchet <pouchet.ohio-state.edu>
 *   Tomofumi Yuki <tomofumi.yuki.fr>
 *
 * Web address: http://polybench.sourceforge.net
 */
/* lu.c: this file is part of PolyBench/C */

//#include <stdio.h>
//#include <unistd.h>
//#include <string.h>
//#include <math.h>

#ifndef SYNTHESIS
#include <stdio.h>
#endif 

#define plus(i) i = i + ONE

static
void init_array (int n,
   int A[40][40])
{
  int ONE = 1;
  int i, j;

  for (i = 0; i < n; plus(i))
    {
      for (j = 0; j <= i; plus(j))
 A[i][j] = (((-j) % n) / n) + ONE;
      for (j = i+1; j < n; plus(j)) {
 A[i][j] = 0;
      }
      A[i][i] = 1;
    }



  int r,s,t;
  int B[40][40]; // B = (int(*)[40 + 0][40 + 0])polybench_alloc_data ((40 + 0) * (40 + 0), sizeof(int));;
  for (r = 0; r < n; plus(r))
    for (s = 0; s < n; plus(s))
      B[r][s] = 0;
  for (t = 0; t < n; plus(t))
    for (r = 0; r < n; plus(r))
      for (s = 0; s < n; plus(s))
 B[r][s] += A[r][t] * A[s][t];
    for (r = 0; r < n; plus(r))
      for (s = 0; s < n; plus(s))
 A[r][s] = B[r][s];
  //free((void*)B);;

}

static
void kernel_lu(int n,
        int A[ 40][40])
{
  int i, j, k;
  int ONE = 1;

 for (i = 0; i < n; plus(i)) {
    for (j = 0; j <i; plus(j)) {
       for (k = 0; k < j; plus(k)) {
          A[i][j] -= A[i][k] * A[k][j];
       }
        A[i][j] = (A[i][j] / A[j][j]);
    }
   for (j = i; j < n; plus(j)) {
       for (k = 0; k < i; plus(k)) {
          A[i][j] -= A[i][k] * A[k][j];
       }
    }
  }
}

static
int check_array(int n,
   int A[40][40])
{
  int res = 0;
  int i, j;
  int ONE = 1;

  for (i = 0; i < n; plus(i))
    for (j = 0; j < n; plus(j)) 
      if(A[i][j] !=0) res = 1;
    #ifndef SYNTHESIS
    printf("finished: %u\n", res);
    #endif 

  return res;
}


int main()
{
  
  int n = 40;


  int A[40][40]; //A = (int(*)[40 + 0][40 + 0])polybench_alloc_data ((40 + 0) * (40 + 0), sizeof(int));;


  init_array (n, A);

  kernel_lu (n, A);

  return check_array(n, A);
  return 0;

  //free((void*)A);;
}
