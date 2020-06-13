int main() {
        int x[2] = {5, 10};
        volatile int sum;
        for(int j=0; j <2; j++)
          sum += x[j];
        return sum;
}
