// ccomp -O3 -o div7_perf examples/perftests/div7.c examples/div7.c -I examples
/*
=== OCaml Benchmark ===
Processed Elements : 1000000
Accepted           : false
Execution Time     : 0.839586 seconds
=== C Benchmark ===                  
Processed Elements : 1000000
Accepted           : false
Execution Time     : 0.002673 seconds
*/
/*
# lscpu | grep -E 'Model name|Architecture|CPU\(s\):|cache'
Architecture:                            x86_64
CPU(s):                                  4
Model name:                              Intel(R) Core(TM) i5-7300U CPU @ 2.60GHz
L1d cache:                               64 KiB (2 instances)
L1i cache:                               64 KiB (2 instances)
L2 cache:                                512 KiB (2 instances)
L3 cache:                                3 MiB (1 instance)
NUMA node0 CPU(s):                       0-3
*/

#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include "div7.h"

#define TEST_SIZE 1000000

int main(void)
{
    dfa_word_t test_vector = malloc(sizeof(dfa_symbol_t) * TEST_SIZE);
    if (!test_vector) {
        fprintf(stderr, "Memory allocation failed.\n");
        return 1;
    }

    for (unsigned long long i = 0; i < TEST_SIZE; i++) {
        test_vector[i] = (dfa_symbol_t)((i * 3ULL + 1ULL) % 10ULL);
    }

    clock_t start = clock();
    int accepted = dfa_accepts(test_vector, TEST_SIZE);
    clock_t end = clock();

    double elapsed = (double)(end - start) / CLOCKS_PER_SEC;

    printf("=== C Benchmark ===\n");
    printf("Processed Elements : %d\n", TEST_SIZE);
    printf("Accepted           : %s\n", accepted ? "true" : "false");
    printf("Execution Time     : %.6f seconds\n", elapsed);

    free(test_vector);
    return 0;
}
