#include <stdio.h>
#include <string.h>

int main(int argc, char **argv, char **envp) {
  if (argc != 2) {
    puts("wrong argc");
    return -1;
  }
  
  if (strncmp(argv[1], "Hello", 5) == 0) {
    puts("Goodbye!");
    return 0;
  }

  puts("wrong key");
  return -2;
}