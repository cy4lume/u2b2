#include <stdlib.h>
#include <stdio.h>

int main(void) {
    int *a = (int*)calloc(5, sizeof(int));

    if (*a == 0) {
        puts("[test_calloc] reachable");
    } else {
        puts("[test_calloc] unreachable");
    }
}