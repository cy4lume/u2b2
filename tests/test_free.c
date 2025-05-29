#include <stdio.h>
#include <stdlib.h>

int main(void) {
    int *mem = (int*)malloc(sizeof(int));
    free(mem);
}