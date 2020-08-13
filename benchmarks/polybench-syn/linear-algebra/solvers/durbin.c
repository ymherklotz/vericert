/**
 * This version is stamped on May 10, 2016
 *
 * Contact:
 *   Louis-Noel Pouchet <pouchet.ohio-state.edu>
 *   Tomofumi Yuki <tomofumi.yuki.fr>
 *
 * Web address: http://polybench.sourceforge.net
 */
/* durbin.c: this file is part of PolyBench/C */


#define plus(i) i = i + ONE
/* Include polybench common header. */
static
void init_array (int n,
   int r[ 40 + 0])
{
  int ONE = 1;
  int i, j;

  for (i = 0; i < n; plus(i))
    {
      r[i] = (n+ONE-i);
    }
}



static
int print_array(int n,
   int y[ 40 + 0])

{
  int ONE = 1;
  int i;
  int res = 0;

  for (i = 0; i < n; plus(i)) {
    res  += y[i];
  }
  return res;
}

static
void kernel_durbin(int n,
     int r[ 40 + 0],
     int y[ 40 + 0])
{
 int z[40];
 int alpha;
 int beta;
 int sum;

  int ONE = 1;
 int i,k;

#pragma scop
 y[0] = -r[0];
 beta = 1;
 alpha = -r[0];

 for (k = 1; k < n; plus(k)) {
   beta = (ONE-alpha*alpha)*beta;
   sum = 0;
   for (i=0; i<k; plus(i)) {
      sum += r[k-i-ONE]*y[i];
   }
   alpha = - (r[k] + sum)/beta;

   for (i=0; i<k; plus(i)) {
      z[i] = y[i] + alpha*y[k-i-ONE];
   }
   for (i=0; i<k; plus(i)) {
     y[i] = z[i];
   }
   y[k] = alpha;
 }
#pragma endscop

}


int main()
{

  int n = 40;


  int r[40 + 0]; 
  int y[40 + 0]; 


  init_array (n, r);

  kernel_durbin (n,
   r,
   y);

  return print_array(n, y);

}
