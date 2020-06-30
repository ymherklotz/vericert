int main() {
    int max = 5;
    int acc = 0;
    int b = 1;
    int c = 2;
    
    for (int i = 0; i < max; i = i + b) {
        acc += i;
    }

    return acc + c;
}
