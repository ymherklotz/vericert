/**
 * This version is stamped on May 10, 2016
 *
 * Contact:
 *   Louis-Noel Pouchet <pouchet.ohio-state.edu>
 *   Tomofumi Yuki <tomofumi.yuki.fr>
 *
 * Web address: http://polybench.sourceforge.net
 */
/* adi.c: this file is part of PolyBench/C */

#ifndef SYNTHESIS
#include <stdio.h>
#endif 

static
void init_array (int n, int u[ 20 + 0][20 + 0])
{
  int i, j;

  for (i = 0; i < n; i++)
    for (j = 0; j < n; j++)
    {
      u[i][j] = (((int)(i + n-j)) / n);
    }
}




static
int print_array(int n, int u[ 20 + 0][20 + 0])
{
  int i, j;
  int res = 0;

  for (i = 0; i < n; i++)
    for (j = 0; j < n; j++) {
      res ^= u[i][j];
    }
#ifndef SYNTHESIS
  printf("finished: %u\n", res);
#endif

  return res;
}
static
void kernel_adi(int tsteps, int n,
                int u[ 20 + 0][20 + 0],
                int v[ 20 + 0][20 + 0],
                int p[ 20 + 0][20 + 0],
                int q[ 20 + 0][20 + 0])
{
  int t, i, j;
  int B1, B2;
  int mul1, mul2;
  int a, b, c, d, e, f;

  B1 = 2;
  B2 = 1;
  mul1 = ((B1 * n * n) / tsteps);
  mul2 = ((B2 * n * n) /tsteps);

  a = -((mul1 / 2));
  b = 1+mul1;
  c = a;
  d = -((mul2 / 2));
  e = 1+mul2;
  f = d;
  int ZERO = 0;

  for (t=1; t<=tsteps; t++) {

    for (i=1; i<n-1; i++) {
      v[ZERO][i] = 1;
      p[i][ZERO] = 0;
      q[i][ZERO] = v[ZERO][i];
      for (j=1; j<n-1; j++) {
        p[i][j] = -(c / (a*p[i][j-1]+b));
        q[i][j] = -((-d*u[j][i-1]+(1+2*d)*u[j][i] - f*u[j][i+1]-a*q[i][j-1]) / (a*p[i][j-1]+b));
      }

      v[n-1][i] = 1;
      for (j=n-2; j>=1; j--) {
        v[j][i] = p[i][j] * v[j+1][i] + q[i][j];
      }
    }

    for (i=1; i<n-1; i++) {
      u[i][ZERO] = 1;
      p[i][ZERO] = 0;
      q[i][ZERO] = u[i][ZERO];
      for (j=1; j<n-1; j++) {
        p[i][j] = -(f / (d*p[i][j-1]+e));
        q[i][j] = ((-a*v[i-1][j]+(1+2*a)*v[i][j] - c*v[i+1][j]-d*q[i][j-1]) / (d*p[i][j-1]+e));
      }
      u[i][n-1] = 1;
      for (j=n-2; j>=1; j--) {
        u[i][j] = p[i][j] * u[i][j+1] + q[i][j];
      }
    }
  }
}

int main()
{

  int n = 20;
  int tsteps = 20;


  int u[20 + 0][20 + 0]; 
  int v[20 + 0][20 + 0]; 
  int p[20 + 0][20 + 0]; 
  int q[20 + 0][20 + 0]; 



  init_array (n, u);

  kernel_adi (tsteps, n, u, v, p, q);

  return print_array(n, u);

}
