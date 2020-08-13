/**
 * This version is stamped on May 10, 2016
 *
 * Contact:
 *   Louis-Noel Pouchet <pouchet.ohio-state.edu>
 *   Tomofumi Yuki <tomofumi.yuki.fr>
 *
 * Web address: http://polybench.sourceforge.net
 */
/* mvt.c: this file is part of PolyBench/C */

#define plus(i) i = i + ONE

static
void init_array(int n,
  int x1[ 40 + 0],
  int x2[ 40 + 0],
  int y_1[ 40 + 0],
  int y_2[ 40 + 0],
  int A[ 40 + 0][40 + 0])
{
  int i, j;
  int ONE = 1;
  int THREE = 3;

  for (i = 0; i < n; plus(i))
    {
      x1[i] = (int) (i % n) / n;
      x2[i] = (int) ((i + ONE) % n) / n;
      y_1[i] = (int) ((i + THREE) % n) / n;
      y_2[i] = (int) ((i + 4) % n) / n;
      for (j = 0; j < n; plus(j))
 A[i][j] = (int) (i*j % n) / n;
    }
}




static
int print_array(int n,
   int x1[ 40 + 0],
   int x2[ 40 + 0])

{
  int i;
  int ONE = 1;
  int res = 0;

  for (i = 0; i < n; plus(i)) {
    res ^= x1[i];
  }

  for (i = 0; i < n; plus(i)) {
    res ^= x2[i];
  }
  return res;
}




static
void kernel_mvt(int n,
  int x1[ 40 + 0],
  int x2[ 40 + 0],
  int y_1[ 40 + 0],
  int y_2[ 40 + 0],
  int A[ 40 + 0][40 + 0])
{
  int i, j;
  int ONE = 1;

#pragma scop
 for (i = 0; i < n; plus(i))
    for (j = 0; j < n; plus(j))
      x1[i] = x1[i] + A[i][j] * y_1[j];
  for (i = 0; i < n; plus(i))
    for (j = 0; j < n; plus(j))
      x2[i] = x2[i] + A[j][i] * y_2[j];
#pragma endscop

}


int main()
{

  int n = 40;


  int A[40 + 0][40 + 0]; 
  int x1[40 + 0]; 
  int x2[40 + 0]; 
  int y_1[40 + 0]; 
  int y_2[40 + 0]; 



  init_array (n,
       x1,
       x2,
       y_1,
       y_2,
       A);


  kernel_mvt (n,
       x1,
       x2,
       y_1,
       y_2,
       A);

  return print_array(n, x1, x2);

}
