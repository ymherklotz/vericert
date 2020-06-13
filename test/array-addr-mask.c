int main() {
  unsigned int x[8] = {1,2,3,4,5,6,7,8};
  unsigned int index = 6;
  unsigned int addr = index & 3;  
  return (x[addr]);
}
