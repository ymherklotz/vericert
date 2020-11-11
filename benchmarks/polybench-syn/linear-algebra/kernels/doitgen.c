/**
 * This version is stamped on May 10, 2016
 *
 * Contact:
 *   Louis-Noel Pouchet <pouchet.ohio-state.edu>
 *   Tomofumi Yuki <tomofumi.yuki.fr>
 *
 * Web address: http://polybench.sourceforge.net
 */
/* doitgen.c: this file is part of PolyBench/C */

#include "../../include/misc.h"

#define plus(i) i = i + ONE
static
void init_array(int nr, int nq, int np,
  int A[ 10 + 0][8 + 0][12 + 0],
  int C4[ 12 + 0][12 + 0])
{
  int i, j, k;
  int ONE = 1;

  for (i = 0; i < nr; plus(i))
    for (j = 0; j < nq; plus(j))
      for (k = 0; k < np; plus(k))
 A[i][j][k] = (int) divider(smodulo((i*j + k), np), np);
  for (i = 0; i < np; plus(i))
    for (j = 0; j < np; plus(j))
      C4[i][j] = (int) divider(smodulo(i*j, np), np);
}


static
int print_array(int nr, int nq, int np,
   int A[ 10 + 0][8 + 0][12 + 0])
{
  int i, j, k;
  int ONE = 1;
  int res = 0;

  for (i = 0; i < nr; plus(i))
    for (j = 0; j < nq; plus(j))
      for (k = 0; k < np; plus(k)) {
      res ^= A[i][j][k];
      }
      return res;
}




void kernel_doitgen(int nr, int nq, int np,
      int A[ 10 + 0][8 + 0][12 + 0],
      int C4[ 12 + 0][12 + 0],
      int sum[ 12 + 0])
{
  int r, q, p, s;
  int ONE = 1;

 for (r = 0; r < nr; plus(r))
    for (q = 0; q < nq; plus(q)) {
      for (p = 0; p < np; plus(p)) {
 sum[p] = 0;
 for (s = 0; s < np; plus(s))
   sum[p] += A[r][q][s] * C4[s][p];
      }
      for (p = 0; p < np; plus(p))
 A[r][q][p] = sum[p];
    }

}


int main()
{

  int nr = 10;
  int nq = 8;
  int np = 12;


  int A[10 + 0][8 + 0][12 + 0]; 
  int sum[12 + 0]; 
  int C4[12 + 0][12 + 0]; 


  init_array (nr, nq, np,
       A,
       C4);


  kernel_doitgen (nr, nq, np,
    A,
    C4,
    sum);



  return print_array(nr, nq, np, A);
}
