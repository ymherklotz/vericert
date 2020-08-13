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

#include <stdio.h>
#include <unistd.h>
#include <string.h>
#include <math.h>

/* Include polybench common header. */
#include<polybench.h>
# 1 "trmm.c"
# 1 "<built-in>" 1
# 1 "<built-in>" 3
# 362 "<built-in>" 3
# 1 "<command line>" 1
# 1 "<built-in>" 2
# 1 "trmm.c" 2
# 1 "utilities/polybench.h" 1
# 30 "utilities/polybench.h"
# 1 "/Applications/Xcode.app/Contents/Developer/Platforms/MacOSX.platform/Developer/SDKs/MacOSX.sdk/usr/include/stdlib.h" 1 3 4
# 31 "utilities/polybench.h" 2
# 231 "utilities/polybench.h"
extern void* polybench_alloc_data(unsigned long long int n, int elt_size);
extern void polybench_free_data(void* ptr);




extern void polybench_flush_cache();
extern void polybench_prepare_instruments();
# 2 "trmm.c" 2


# 1 "./linear-algebra/blas/trmm/trmm.h" 1
# 5 "trmm.c" 2



static
void init_array(int m, int n,
  int *alpha,
  int A[ 20 + 0][20 + 0],
  int B[ 20 + 0][30 + 0])
{
  int i, j;

  *alpha = 1.5;
  for (i = 0; i < m; i++) {
    for (j = 0; j < i; j++) {
      A[i][j] = (int)((i+j) % m)/m;
    }
    A[i][i] = 1.0;
    for (j = 0; j < n; j++) {
      B[i][j] = (int)((n+(i-j)) % n)/n;
    }
 }

}




static
void print_array(int m, int n,
   int B[ 20 + 0][30 + 0])
{
  int i, j;

  fprintf(stderr, "==BEGIN DUMP_ARRAYS==\n");
  fprintf(stderr, "begin dump: %s", "B");
  for (i = 0; i < m; i++)
    for (j = 0; j < n; j++) {
 if ((i * m + j) % 20 == 0) fprintf (stderr, "\n");
 fprintf (stderr, "%d ", B[i][j]);
    }
  fprintf(stderr, "\nend   dump: %s\n", "B");
  fprintf(stderr, "==END   DUMP_ARRAYS==\n");
}




static
void kernel_trmm(int m, int n,
   int alpha,
   int A[ 20 + 0][20 + 0],
   int B[ 20 + 0][30 + 0])
{
  int i, j, k;
# 68 "trmm.c"
#pragma scop
 for (i = 0; i < m; i++)
     for (j = 0; j < n; j++) {
        for (k = i+1; k < m; k++)
           B[i][j] += A[k][i] * B[k][j];
        B[i][j] = alpha * B[i][j];
     }
#pragma endscop

}


int main(int argc, char** argv)
{

  int m = 20;
  int n = 30;


  int alpha;
  int (*A)[20 + 0][20 + 0]; A = (int(*)[20 + 0][20 + 0])polybench_alloc_data ((20 + 0) * (20 + 0), sizeof(int));;
  int (*B)[20 + 0][30 + 0]; B = (int(*)[20 + 0][30 + 0])polybench_alloc_data ((20 + 0) * (30 + 0), sizeof(int));;


  init_array (m, n, &alpha, *A, *B);


                             ;


  kernel_trmm (m, n, alpha, *A, *B);


                            ;
                             ;



  if (argc > 42 && ! strcmp(argv[0], "")) print_array(m, n, *B);


  free((void*)A);;
  free((void*)B);;

  return 0;
}
