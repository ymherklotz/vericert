int main() {
    int a[10] = {0};

    for (int i = 1; i < 10; i++) {
        a[i] = a[i-1] + i;
    }

    return a[9];
}
