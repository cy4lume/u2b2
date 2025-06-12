#include <stdio.h>

int inc(int v){ return v+1; }
int foo(int a){
    if (a == inc(a)) {
        return 42; 
    }
    return 0;
}

int main(void) {
    int x;
    
    return foo(x);
}