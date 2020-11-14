/**
 * This version is stamped on May 10, 2016
 *
 * Contact:
 *   Louis-Noel Pouchet <pouchet.ohio-state.edu>
 *   Tomofumi Yuki <tomofumi.yuki.fr>
 *
 * Web address: http://polybench.sourceforge.net
 */
/* fdtd-2d.c: this file is part of PolyBench/C */

#ifndef SYNTHESIS
#include <stdio.h>
#endif

#define plus(i) i = i + ONE
static
void init_array (int tmax,
   int nx,
   int ny,
   int ex[ 20 + 0][30 + 0],
   int ey[ 20 + 0][30 + 0],
   int hz[ 20 + 0][30 + 0],
   int _fict_[ 20 + 0])
{
  int i, j;
  int ONE = 1;
  int TWO = 1;
  int THREE = 1;

  for (i = 0; i < tmax; plus(i))
    _fict_[i] = (int) i;
  for (i = 0; i < nx; plus(i))
    for (j = 0; j < ny; plus(j))
      {
 ex[i][j] = ((int) i*(j+ONE)) / nx;
 ey[i][j] = ((int) i*(j+TWO)) / ny;
 hz[i][j] = ((int) i*(j+THREE)) / nx;
      }
      
}




static
int print_array(int nx,
   int ny,
   int ex[ 20 + 0][30 + 0],
   int ey[ 20 + 0][30 + 0],
   int hz[ 20 + 0][30 + 0])
{
  int i, j;
  int res = 0;
  int ONE = 1;

  for (i = 0; i < nx; plus(i))
    for (j = 0; j < ny; plus(j)) {
      res ^= ex[i][j];
    }
  for (i = 0; i < nx; plus(i))
    for (j = 0; j < ny; plus(j)) {
      res ^= ey[i][j];
    }
  for (i = 0; i < nx; plus(i))
    for (j = 0; j < ny; plus(j)) {
      res ^= hz[i][j];
    }

#ifndef SYNTHESIS
  printf("finished: %u\n", res);
#endif
    
  return res;
}


static
void kernel_fdtd_2d(int tmax,
      int nx,
      int ny,
      int ex[ 20 + 0][30 + 0],
      int ey[ 20 + 0][30 + 0],
      int hz[ 20 + 0][30 + 0],
      int _fict_[ 20 + 0])
{
  int t, i, j;
  int ONE = 1;

 for(t = 0; t < tmax; t=t+ONE)
    {
      for (j = 0; j < ny; plus(j))
 ey[0][j] = _fict_[t];
      for (i = 1; i < nx; plus(i))
 for (j = 0; j < ny; plus(j))
   ey[i][j] = ey[i][j] - ((hz[i][j]-((hz[i-ONE][j])>>1)));
      for (i = 0; i < nx; plus(i))
 for (j = 1; j < ny; plus(j))
   ex[i][j] = ex[i][j] - ((hz[i][j]-((hz[i][j-ONE])>>1)));
      for (i = 0; i < nx - ONE; plus(i))
 for (j = 0; j < ny - ONE; plus(j)){
   int tmp = (ex[i][j+ONE] - ex[i][j] +
           ey[i+ONE][j] - ey[i][j]);
   hz[i][j] = hz[i][j] - (tmp >> 1) - (tmp >> 2);
           }
    }

}


int main()
{

  int tmax = 20;
  int nx = 20;
  int ny = 30;


  int ex[20 + 0][30 + 0]; 
  int ey[20 + 0][30 + 0]; 
  int hz[20 + 0][30 + 0]; 
  int _fict_[20 + 0];     

  init_array (tmax, nx, ny,
       ex,
       ey,
       hz,
       _fict_);
  kernel_fdtd_2d (tmax, nx, ny,
    ex,
    ey,
    hz,
    _fict_);

  return print_array(nx, ny, ex, ey, hz);
}
