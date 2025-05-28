#include <stdlib.h>
#include <string.h>

int main(void) {
    int *x = (int *)malloc(sizeof(int) * 6);
    memset(x, 0, 6);
}