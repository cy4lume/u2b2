#include <stdio.h>
#include <stdlib.h>
#include <string.h>

int main(void) {
    char str1[30] = "Hello, world!\n";
    char str2[30] = {0, };

    memcpy(str2, str1, 5);
}