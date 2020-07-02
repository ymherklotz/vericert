int main() {
    int x[3] = {1, 2, 3};
    int sum = 0, incr = 1;
    for (int i = 0; i < 3; i=i+incr)
        sum += x[i];
    return sum;
}
