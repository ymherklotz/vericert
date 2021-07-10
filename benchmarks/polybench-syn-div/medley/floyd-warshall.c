/**
 * This version is stamped on May 10, 2016
 *
 * Contact:
 *   Louis-Noel Pouchet <pouchet.ohio-state.edu>
 *   Tomofumi Yuki <tomofumi.yuki.fr>
 *
 * Web address: http://polybench.sourceforge.net
 */
/* floyd-warshall.c: this file is part of PolyBench/C */

#ifndef SYNTHESIS
  #include <stdio.h>
#endif

#define plus(i) i = i + ONE
static
void init_array (int n,
   int path[ 60 + 0][60 + 0])
{
  int i, j;
  int ONE = 1;

  for (i = 0; i < n; plus(i))
    for (j = 0; j < n; plus(j)) {
      path[i][j] = i*(j % (ONE+6))+ONE;
      //if (((i+j)%13 == ZERO || (i+j)%7== ZERO || (i+j)%11 == ZERO ) != 0 )
      if(((((i+j) % (12+ONE)) == (int)0 || ((i+j) % (ONE+6)) == (int)0)!=0 || ((i+j) % (10+ONE)) == (int)0 ) != 0)
         path[i][j] = 999;
    }
}




static
int print_array(int n,
   int path[ 60 + 0][60 + 0])

{
  int i, j;
  int res = 0;
  int ONE = 1;

  for (i = 0; i < n; plus(i))
    for (j = 0; j < n; plus(j)) {
      res ^= path[i][j];
    }
#ifndef SYNTHESIS
  printf("finished %u\n", res);
#endif
  return res;
}




static
void kernel_floyd_warshall(int n,
      int path[ 60 + 0][60 + 0])
{
  int i, j, k;
  int ONE = 1;

 for (k = 0; k < n; plus(k))
    {
      for(i = 0; i < n; plus(i))
 for (j = 0; j < n; plus(j))
   path[i][j] = path[i][j] < path[i][k] + path[k][j] ?
     path[i][j] : path[i][k] + path[k][j];
    }

}


int main()
{

  int n = 60;


  int path[60 + 0][60 + 0]; 

  init_array (n, path);

  kernel_floyd_warshall (n, path);

  return print_array(n, path);

  return 0;
}
