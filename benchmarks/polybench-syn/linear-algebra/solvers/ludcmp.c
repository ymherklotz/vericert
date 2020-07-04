/**
 * This version is stamped on May 10, 2016
 *
 * Contact:
 *   Louis-Noel Pouchet <pouchet.ohio-state.edu>
 *   Tomofumi Yuki <tomofumi.yuki.fr>
 *
 * Web address: http://polybench.sourceforge.net
 */
/* ludcmp.c: this file is part of PolyBench/C */

#define plus(i) i = i + ONE

static
void init_array (int n,
   int A[ 40 + 0][40 + 0],
   int b[ 40 + 0],
   int x[ 40 + 0],
   int y[ 40 + 0])
{
  int i, j;
  int ONE = 1;
  int TWO = 2;
  int FOUR = 4;
  int fn = (int)n;

  for (i = 0; i < n; plus(i))
    {
      x[i] = 0;
      y[i] = 0;
      b[i] = (i+ONE)/fn/(TWO) + (FOUR);
    }

  for (i = 0; i < n; plus(i))
    {
      for (j = 0; j <= i; plus(j))
 A[i][j] = (int)(-j % n) / n + ONE;
      for (j = i+ONE; j < n; plus(j)) {
 A[i][j] = 0;
      }
      A[i][i] = 1;
    }



  int r,s,t;
  int B[40 + 0][40 + 0]; 
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

}




static
int check_array(int n,
   int x[ 40 + 0])

{
  int i;
  int ONE = 1;
  int res = 0;

  for (i = 0; i < n; plus(i)) {
  res += x[i];
  }
  return res;
}




static
void kernel_ludcmp(int n,
     int A[ 40 + 0][40 + 0],
     int b[ 40 + 0],
     int x[ 40 + 0],
     int y[ 40 + 0])
{
  int i, j, k;
  int ONE = 1;

  int w;

#pragma scop
 for (i = 0; i < n; plus(i)) {
    for (j = 0; j <i; plus(j)) {
       w = A[i][j];
       for (k = 0; k < j; plus(k)) {
          w -= A[i][k] * A[k][j];
       }
        A[i][j] = w / A[j][j];
    }
   for (j = i; j < n; plus(j)) {
       w = A[i][j];
       for (k = 0; k < i; plus(k)) {
          w -= A[i][k] * A[k][j];
       }
       A[i][j] = w;
    }
  }

  for (i = 0; i < n; plus(i)) {
     w = b[i];
     for (j = 0; j < i; plus(j))
        w -= A[i][j] * y[j];
     y[i] = w;
  }

   for (i = n-ONE; i >=0; i=i-ONE) {
     w = y[i];
     for (j = i+ONE; j < n; plus(j))
        w -= A[i][j] * x[j];
     x[i] = w / A[i][i];
  }
#pragma endscop

}


int main()
{

  int n = 40;
  int ONE = 1;


  int A[40 + 0][40 + 0]; 
  int b[40 + 0];
  int x[40 + 0];
  int y[40 + 0];



  init_array (n,
       A,
       b,
       x,
       y);


                             ;


  kernel_ludcmp (n,
   A,
   b,
   x,
   y);

  return check_array(n, x);


  return 0;
}
