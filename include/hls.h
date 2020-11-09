#ifndef VERICERT_HLS_H
#define VERICERT_HLS_H

/*
 * Divider C implementation for faster frequency division.
 */
unsigned divider_fast(unsigned x, unsigned y) {
    unsigned r0, q0, y0, y1;

    r0 = x;
    q0 = 0;
    y0 = y;
    y1 = y;
    do {
        y1 = 2 * y1;
    } while (y1 <= x);
    do {
        y1 /= 2;
        q0 *= 2;
        if (r0 >= y1) {
            r0 -= y1;
            q0++;
        }
    } while ((int)y1 != (int)y0);
    return q0;
}

unsigned divider(unsigned x, unsigned y) {
    unsigned q0, acc;
    q0 = 0;
    acc = y;

    while (acc <= x) {
        q0++;
        acc += y;
    }

    return q0;
}

/*
 * Signed division operation for faster frequency division.
 */
int sdivider(int N, int D) {
    if (D < 0) {
        if (N < 0)
            return divider(-N, -D);
        else
            return -divider(N, -D);
    } else {
        if (N < 0)
            return -divider(-N, D);
        else
            return divider(N, D);
    }
}

int sdivider_fast(int N, int D) {
    if (D < 0) {
        if (N < 0)
            return divider_fast(-N, -D);
        else
            return -divider_fast(N, -D);
    } else {
        if (N < 0)
            return -divider_fast(-N, D);
        else
            return divider_fast(N, D);
    }
}

#endif
