/**
 * This version is stamped on May 10, 2016
 *
 * Contact:
 *   Louis-Noel Pouchet <pouchet.ohio-state.edu>
 *   Tomofumi Yuki <tomofumi.yuki.fr>
 *
 * Web address: http://polybench.sourceforge.net
 */
/* syrk.c: this file is part of PolyBench/C */


#define plus(i) i = i + ONE
static
void init_array(int n, int m,
  int *alpha,
  int *beta,
  int C[ 30 + 0][30 + 0],
  int A[ 30 + 0][20 + 0])
{
  int i, j;
  int ONE = 1;

  *alpha = 3;
  *beta = 2;
  for (i = 0; i < n; plus(i))
    for (j = 0; j < m; plus(j))
      A[i][j] = (int) ((i*j+ONE)%n) / n;
  for (i = 0; i < n; plus(i))
    for (j = 0; j < n; plus(j))
      C[i][j] = (int) ((i*j+ONE+ONE)%m) / m;
}


static
int print_array(int n,
   int C[ 30 + 0][30 + 0])
{
  int i, j;
  int ONE = 1;
  int res = 0;

  for (i = 0; i < n; plus(i))
    for (j = 0; j < n; plus(j)) {
      res ^= C[i][j];
    }
  return res;
}




static
void kernel_syrk(int n, int m,
   int alpha,
   int beta,
   int C[ 30 + 0][30 + 0],
   int A[ 30 + 0][20 + 0])
{
  int i, j, k;
  int ONE = 1;

#pragma scop
 for (i = 0; i < n; plus(i)) {
    for (j = 0; j <= i; plus(j))
      C[i][j] *= beta;
    for (k = 0; k < m; plus(k)) {
      for (j = 0; j <= i; plus(j))
        C[i][j] += alpha * A[i][k] * A[j][k];
    }
  }
#pragma endscop

}


int main()
{

  int n = 30;
  int m = 20;


  int alpha;
  int beta;
  int C[30 + 0][30 + 0]; 
  int A[30 + 0][20 + 0]; 


  init_array (n, m, &alpha, &beta, C, A);


                             ;


  kernel_syrk (n, m, alpha, beta, C, A);


                            ;
                             ;



  return print_array(n, C);

}
