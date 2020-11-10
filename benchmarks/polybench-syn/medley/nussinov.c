/**
 * This version is stamped on May 10, 2016
 *
 * Contact:
 *   Louis-Noel Pouchet <pouchet.ohio-state.edu>
 *   Tomofumi Yuki <tomofumi.yuki.fr>
 *
 * Web address: http://polybench.sourceforge.net
 */
/* nussinov.c: this file is part of PolyBench/C */

typedef int base; 

#define plus(i) i = i + ONE
static
void init_array (int n,
                 base seq[ 60 + 0],
   int table[ 60 + 0][60 + 0])
{
  int i, j;
  int ONE = 1;
  int FOUR = 4;


  for (i=0; i <n; plus(i)) {
     seq[i] = (base)((i+ONE)%FOUR);
  }

  for (i=0; i <n; plus(i))
     for (j=0; j <n; plus(j))
       table[i][j] = 0;
}




static
int print_array(int n,
   int table[ 60 + 0][60 + 0])

{
  int i, j;
  int ONE = 1;
  int res = 0;

  for (i = 0; i < n; plus(i)) {
    for (j = i; j < n; plus(j)) {
      res ^= table[i][j];
    }
  }
  return res;
}

static
void kernel_nussinov(int n, base seq[ 60 + 0],
      int table[ 60 + 0][60 + 0])
{
  int i, j, k;
  int ZERO = 0;
  int ONE = 1;
  int THREE = 3;

#pragma scop
 for (i = n-ONE; i >= ZERO; i=i-ONE) {
  for (j=i+ONE; j<n; plus(j)) {

   if (j-ONE>=ZERO)
      table[i][j] = ((table[i][j] >= table[i][j-ONE]) ? table[i][j] : table[i][j-ONE]);
   if (i+ONE<n)
      table[i][j] = ((table[i][j] >= table[i+ONE][j]) ? table[i][j] : table[i+ONE][j]);

   if ((j-ONE>=ZERO && i+ONE<n) !=  (int)0) {

     if (i<j-ONE)
        table[i][j] = ((table[i][j] >= table[i+ONE][j-ONE]+(((seq[i])+(seq[j])) == THREE ? ONE : ZERO)) ? table[i][j] : table[i+ONE][j-ONE]+(((seq[i])+(seq[j])) == THREE ? ONE : ZERO));
     else
        table[i][j] = ((table[i][j] >= table[i+ONE][j-ONE]) ? table[i][j] : table[i+ONE][j-ONE]);
   }

   for (k=i+ONE; k<j; plus(k)) {
      table[i][j] = ((table[i][j] >= table[i][k] + table[k+ONE][j]) ? table[i][j] : table[i][k] + table[k+ONE][j]);
   }
  }
 }
#pragma endscop

}


int main()
{

  int n = 60;


  base (seq)[60 + 0];           
  int (table)[60 + 0][60 + 0];  


  init_array (n, seq, table);

  kernel_nussinov (n, seq, table);

  return print_array(n, table);

}
