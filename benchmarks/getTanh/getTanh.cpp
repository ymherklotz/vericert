/*

	Function Name: getTanh
	Description: This function takes one input array and generates getTanh result for each elements.
	Source: https://github.com/JianyiCheng/HLS-benchmarks/blob/master/DSS/getTanh/src/inlined.cpp
	
*/

void getTanh(int A[1000], int atanh[12], int sinh[5], int cosh[5]){
    int i;

    // the result is positive or negative
    int is_neg;
    // Input angle
    int beta;
    // Output of the hyperbolic CORDIC block
    int outputcosh, outputsinh;
    // Result of tanh, sinh and cosh
    int result;
    // Token for the repetition of the 4th iteration
    //char token4 = 0;
    // Approximation of cosh(beta) and sinh(beta)
    int x = 0x1351;
    int y = 0;
    int x_new;
    int j, k;
    int index_trigo;
    int  result_cosh, result_sinh;

  for (i = 0; i < 1000; i++){
       beta = A[i];

        // Implement approximate range of the hyperbolic CORDIC block
        if (beta >= 20480) {
          result = 4096; // Saturation effect
        } else {
	  if (beta >= 16384) {
            index_trigo = 4;
          } else if (beta >= 12288) {
            index_trigo = 3;
          } else if (beta >= 8192) {
            index_trigo = 2;
          } else if (beta >= 4096) {
            index_trigo = 1;
          } else {
            index_trigo = 0;
          }
          beta = beta - index_trigo * 4096;
          // Call to the hyperbolic CORDIC block
          x = 0x1351;
          y = 0;
          fp_hyp_cordic:
          for (k = 1; k <= 12; k++) {
            // force the 3k+1 th iteration to be repeated
            if (((k%3)==1) &&( k!=1 )){
              for (j=1;j<=2;j++){
                // beta<0 anti-clockwise rotation
                if (beta < 0) {
                  x_new = x - (y >> k);
                  y -= x >> k;
                  beta += atanh[k - 1];
                }
                // beta>0 clockwise rotation
                else {
                  x_new = x + (y >> k);
                  y += (x >> k);
                  beta -= atanh[k - 1];
                }
                x = x_new;
              }
            }
          else {
              if (beta < 0) {
                x_new = x - (y >> k);
                y -= x >> k;
                beta += atanh[k - 1];
              }
              // beta>0 clockwise rotation
              else {
                x_new = x + (y >> k);
                y += (x >> k);
                beta -= atanh[k - 1];
              }
              x = x_new;
            }
          }
	  outputcosh = x;
          outputsinh = y;

          // Trigonometric rules application
          result_cosh = (sinh[index_trigo] * outputcosh + cosh[index_trigo] * outputsinh);
          result_sinh = (cosh[index_trigo] * outputcosh + sinh[index_trigo] * outputsinh) >> 12;
          result = result_cosh / result_sinh;
        }

        A[i] = result;
  }

}

int main(){

    int atanh[12] = { 0x08C9, 0x0416, 0x0202, 0x0100, 0x0080, 0x0064, 0x0032, 0x0010, 0x0008, 0x0004, 0x0002, 0x0001 };
    int cosh[5] = { 0x1000, 0x18B0, 0x3C31, 0xA115, 0x1B4EE};
    int sinh[5] = { 0x0, 0x12CD, 0x3A07, 0xA049, 0x1B4A3};
    
    int A[1000];

    for (int i = 0; i < 1000; i++)
        A[i] = i; 	// here you can change your input data as you wish.
    

    getTanh(A, atanh, sinh, cosh);
    
}