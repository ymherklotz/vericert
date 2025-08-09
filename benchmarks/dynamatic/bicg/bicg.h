#pragma once

typedef float in_float_t;
typedef float inout_float_t;

#define N 30

int bicg(int A[N][N], int s[N], int q[N],  int p[N], int r[N]);
