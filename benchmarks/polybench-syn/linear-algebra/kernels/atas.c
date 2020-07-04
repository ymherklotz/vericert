/**
 * This version is stamped on May 10, 2016
 *
 * Contact:
 *   Louis-Noel Pouchet <pouchet.ohio-state.edu>
 *   Tomofumi Yuki <tomofumi.yuki.fr>
 *
 * Web address: http://polybench.sourceforge.net
 */
/* atax.c: this file is part of PolyBench/C */

#define plus(i) i = i + ONE
static
void init_array (int m, int n,
   int A[ 38 + 0][42 + 0],
   int x[ 42 + 0])
{
  int ONE = 1;
  int i, j;
  int fn;
  fn = (int)n;

  for (i = 0; i < n; plus(i))
      x[i] = ONE + (i / fn);
  for (i = 0; i < m; plus(i))
    for (j = 0; j < n; plus(j))
      A[i][j] = (int) ((i+j) % n) / (5*m);
}




static
int print_array(int n,
   int y[ 42 + 0])

{
  int i;
  int ONE = 1;
  int res = 0;

  for (i = 0; i < n; plus(i)) {
    res ^= y[i];
  }
  return res;
}




static
void kernel_atax(int m, int n,
   int A[ 38 + 0][42 + 0],
   int x[ 42 + 0],
   int y[ 42 + 0],
   int tmp[ 38 + 0])
{
  int i, j;
  int ONE = 1;

#pragma scop
 for (i = 0; i < n; plus(i))
    y[i] = 0;
  for (i = 0; i < m; plus(i))
    {
      tmp[i] = 0;
      for (j = 0; j < n; plus(j))
 tmp[i] = tmp[i] + A[i][j] * x[j];
      for (j = 0; j < n; plus(j))
 y[j] = y[j] + A[i][j] * tmp[i];
    }
#pragma endscop

}


int main()
{

  int m = 38;
  int n = 42;


  int A[38 + 0][42 + 0]; 
  int x[42 + 0]; 
  int y[42 + 0]; 
  int tmp[38 + 0]; 

  init_array (m, n, A, x);

  kernel_atax (m, n,
        A,
        x,
        y,
        tmp);


  return print_array(n, y);

}
