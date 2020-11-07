#ifndef VERICERT_HLS_H
#define VERICERT_HLS_H

/*
 * Divider C implementation for faster frequency division.
 */
unsigned int divider(unsigned int x, unsigned int y) {
    unsigned int r0, q0, y0, y1;

    r0 = x;
    q0 = 0;
    y0 = y;
    y1 = y;
    do {
        y1 = 2 * y1;
    } while (y1 <= x);
    do {
        y1 = y1 / 2;
        q0 = 2 * q0;
        if (r0 >= y1) {
            r0 = r0 - y1;
            q0 = q0 + 1;
        }
    } while ((int)y1 != (int)y0);
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

#endif
