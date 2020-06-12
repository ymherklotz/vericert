// source: https://github.com/LegUpComputing/legup-examples/tree/master/tutorials/sobel

#include <stdio.h>
#include <stdlib.h>
#include "input.h"
#include "output.h"

#define WIDTH 512
#define HEIGHT 512

void sobel_filter(unsigned char input[][WIDTH],
                  unsigned char output[][WIDTH]) {
    int i, j;
    int m, n;

    int gx_sum, gy_sum, sum;

    int gx[3][3] = {{-1, 0, 1},
                    {-2, 0, 2},
                    {-1, 0, 1}};

    int gy[3][3] = {{ 1,  2,  1},
                    { 0,  0,  0},
                    {-1, -2, -1}};

    for (i = 0; i < HEIGHT; i++) {
        for (j = 0; j < WIDTH; j++) {
            sum = 0;
            int outofbounds = 0;
            outofbounds |= (i < 1) | (i > (HEIGHT - 2));
            outofbounds |= (j < 1) | (j > (WIDTH - 2));

            gx_sum = 0;
            gy_sum = 0;
            for (m = -1; m <= 1; m++) {
                for (n = -1; n <= 1; n++) {
                    gx_sum += (outofbounds) ? 0 :
                        ((int)input[i + m][j + n]) * gx[m + 1][n + 1];
                    gy_sum += (outofbounds) ? 0 :
                        ((int)input[i + m][j + n]) * gy[m + 1][n + 1];
                }
            }

            gx_sum = (gx_sum < 0) ? -gx_sum : gx_sum;
            gy_sum = (gy_sum < 0) ? -gy_sum : gy_sum;

            sum = gx_sum + gy_sum;
            sum = (sum > 255) ? 255 : sum;

            output[i][j] = (unsigned int)sum;
        }
    }
}

int main()
{
    unsigned char sobel_output[HEIGHT][WIDTH];

    sobel_filter(elaine_512_input, sobel_output);

    int result = 0;
    int i, j;

    for(i = 0; i < HEIGHT; i++) {
        for(j = 0; j < WIDTH; j++){
            if( sobel_output[i][j] != elaine_512_golden_output[i][j])
                result++;
        }
    }

    if (!result)
        printf("PASS!\n");
    else
        printf("FAIL with %d differences\n", result);

    return result;
}
