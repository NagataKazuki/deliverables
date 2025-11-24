#include <stdio.h>

int main() {
    int f0 = 0;
    int f1 = 0;
    int f2 = 0;
    int f3 = 1;
    int i = 1;

    while (i < 10) {
        f0 = f3 + f1 + f2;
        f3 = f2;
        f2 = f1;
        f1 = f0;
        i++;
    }

    printf("f0 = %d\n", f0); 

    return 0;
}

