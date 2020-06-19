#define N 4

void matrix_multiply(int first[N][N], int second[N][N], int multiply[N][N]) {
    int sum = 0;
    for (int c = 0; c < N; c++) {
        for (int d = 0; d < N; d++) {
            for (int k = 0; k < N; k++) {
                sum = sum + first[c][k]*second[k][d];
            }
            multiply[c][d] = sum;
            sum = 0;
        }
    }
}

int main() {
    int f[N][N] = {{1, 2, 3, 4}, {1, 2, 3, 4}, {1, 2, 3, 4}, {1, 2, 3, 4}};
    int s[N][N] = {{5, 6, 7, 8}, {5, 6, 7, 8}, {5, 6, 7, 8}, {5, 6, 7, 8}};
    int m[N][N] = {{0, 0, 0, 0}, {0, 0, 0, 0}, {0, 0, 0, 0}, {0, 0, 0, 0}};

    matrix_multiply(f, s, m);
    return m[1][1];
}
