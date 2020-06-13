int main() {
        int index[2] = {1, 0};
        int x[2] = {5, 10};
        int y[2] = {0, 0};
        for(int i=0; i<2;i++){
          y[i] = x[index[i]] * (i+1);
        }

        int sum = 0;
        for(int j=0; j <2; j++)
          sum += y[j];
        return sum;
}
