// ccomp -O3 -o mod3_perf examples/perftests/mod3.c examples/mod3.c -I examples/
/*
=== OCaml Benchmark ===
Processed Elements : 1000000
Accepted           : false
Execution Time     : 0.179735 seconds
=== C Benchmark ===                  
Processed Elements : 1000000
Accepted           : false
Execution Time     : 0.002200 seconds
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
#include "mod3.h"

#define TEST_SIZE 1000000

int main(void)
{
    dfa_word_t test_vector = malloc(sizeof(dfa_symbol_t) * TEST_SIZE);
    if (!test_vector) {
        fprintf(stderr, "Memory allocation failed.\n");
        return 1;
    }

    // Populate with heavy stream of 1s to continuously cycle through mod 3 states
    for (unsigned long long i = 0; i < TEST_SIZE; i++) {
        test_vector[i] = (dfa_symbol_t)(i % 2ULL); // Mixture of 0 and 1
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
