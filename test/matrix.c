void matrix_multiply(int first[2][2], int second[2][2], int multiply[2][2]) {
    int sum = 0;
    for (int c = 0; c < 2; c++) {
        for (int d = 0; d < 2; d++) {
            for (int k = 0; k < 2; k++) {
                sum = sum + first[c][k]*second[k][d];
            }
            multiply[c][d] = sum;
            sum = 0;
        }
    }
}

int main() {
    int f[2][2] = {{1, 2}, {3, 4}};
    int s[2][2] = {{5, 6}, {7, 8}};
    int m[2][2] = {{0, 0}, {0, 0}};

    matrix_multiply(f, s, m);
    return m[1][1];
}
