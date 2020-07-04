/**
 * This version is stamped on May 10, 2016
 *
 * Contact:
 *   Louis-Noel Pouchet <pouchet.ohio-state.edu>
 *   Tomofumi Yuki <tomofumi.yuki.fr>
 *
 * Web address: http://polybench.sourceforge.net
 */
/* covariance.c: this file is part of PolyBench/C */

#define plus(i) i = i + ONE
static
void init_array (int m, int n,
   int *float_n,
   int data[ 32 + 0][28 + 0])
{
  int i, j;
  int ONE = 1;

  *float_n = (int)n;

  for (i = 0; i < 32; plus(i))
    for (j = 0; j < 28; plus(j))
      data[i][j] = ((int) i*j) / 28;
}




static
int print_array(int m,
   int cov[ 28 + 0][28 + 0])

{
  int i, j;
  int ONE = 1;
  int res = 0;
  for (i = 0; i < m; plus(i))
    for (j = 0; j < m; plus(j)) {
      res ^= cov[i][j];
    }
    return res;
}




static
void kernel_covariance(int m, int n,
         int float_n,
         int data[ 32 + 0][28 + 0],
         int cov[ 28 + 0][28 + 0],
         int mean[ 28 + 0])
{
  int i, j, k;
  int ONE = 1;

#pragma scop
 for (j = 0; j < m; plus(j))
    {
      mean[j] = 0;
      for (i = 0; i < n; plus(i))
        mean[j] += data[i][j];
      mean[j] /= float_n;
    }

  for (i = 0; i < n; plus(i))
    for (j = 0; j < m; plus(j))
      data[i][j] -= mean[j];

  for (i = 0; i < m; plus(i))
    for (j = i; j < m; plus(j))
      {
        cov[i][j] = 0;
        for (k = 0; k < n; plus(k))
   cov[i][j] += data[k][i] * data[k][j];
        cov[i][j] /= (float_n - ONE);
        cov[j][i] = cov[i][j];
      }
#pragma endscop

}


int main()
{

  int n = 32;
  int m = 28;


  int float_n;
  int data[32 + 0][28 + 0];
  int mean[28 + 0]; 
  int cov[28 + 0][28 + 0]; 

  init_array (m, n, &float_n, data);

  kernel_covariance (m, n, float_n,
       data,
       cov,
       mean);

  return print_array(m, cov);

}
