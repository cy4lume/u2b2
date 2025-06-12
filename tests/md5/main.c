#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>

#include "md5.h"

void print_hash(uint8_t *p){
    for(unsigned int i = 0; i < 16; ++i){
        printf("%02x", p[i]);
    }
    printf("\n");
}

int main(){
    uint8_t result[16];
    md5String("Hello, world!", result);
    print_hash(result);
}
