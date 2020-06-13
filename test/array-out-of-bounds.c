int main() {
        int x[2] = {1, 2};
        int y[2] = {3, 4};
        x[2] = 0;
        int sum = 0;
        for(int i=0; i<2; i++)
          sum += (x[i] * y[i]);
  return sum;
}
