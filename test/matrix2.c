void matrix_multiply(int first[][2], int second[][2], int multiply[][2], int m, int q, int p, int *totalSum) {
    int sum = 0;
    for (int c = 0; c < m; c++) {
        for (int d = 0; d < q; d++) {
            for (int k = 0; k < p; k++) {
                sum = sum + first[c][k]*second[k][d];
            }
            multiply[c][d] = sum;
            *totalSum += sum;
            sum = 0;
        }
    }
}

int main() {
    int f[2][2] = {{1, 2}, {3, 4}};
    int s[2][2] = {{1, 2}, {3, 4}};
    int m[2][2] = {{0, 0}, {0, 0}};
    int sum = 0;

    matrix_multiply(f, s, m, 2, 2, 2, &sum);
    return sum;
}
