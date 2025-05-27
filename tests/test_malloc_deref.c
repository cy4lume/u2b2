#include <stdio.h>
#include <stdlib.h>

int main(){
    int *x = (int*)malloc(sizeof(int));

    if (*x > 0) {
        puts("reachable");
    }
}