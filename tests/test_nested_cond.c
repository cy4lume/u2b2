#include <stdio.h>

int main(void) {
    int x;

    if (x > 3) {
        puts("[x > 3] reachable");
        if (x == 3) {
            puts("[And(x > 3, x == 3)] unreachable");
        }
    } else if (x == 3) {
        puts("[x == 3] reachable");
        if (x > 3) {
            puts("[And(x == 3, x > 3)] unreachable");
        }
    } else if (x < 3) {
        puts("[x < 3] reachable");
    } else {
        puts("[else] unreachable");
    }
}