#include <stdio.h>

int inc(int x) {
  return x + 1;
}

int func1(int a, int b) {
  if (a == 42) {
    return 0;
  }

  if (a == inc(a)) {
    // dead
    return 0x4242;
  }

  return 1;
}

int dead_func(int a, int b) {
  if (a == 42) {
    return 0;
  }

  return 1;
}

int main(int argc, int **argv, char **envp) {
  if (argc != 3) {
    puts("wrong argc");
    return -1;
  }
  int a;
  int b;

  return func1(a, b);
}