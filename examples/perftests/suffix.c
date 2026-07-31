// ccomp -O3 -o suffix_perf examples/perftests/suffix.c examples/suffix.c -I examples/
/*
=== OCaml Benchmark ===
Processed Elements : 1000000
Accepted           : false
Execution Time     : 0.288550 seconds
=== C Benchmark ===                  
Processed Elements : 1000000
Accepted           : false
Execution Time     : 0.008649 seconds
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
#include "suffix.h"

#define TEST_SIZE 1000000
#define NUM_TESTS 100

int main(void)
{
    int accepted;
    nfa_word_t test_vector = malloc(sizeof(nfa_symbol_t) * TEST_SIZE);
    if (!test_vector) {
        fprintf(stderr, "Memory allocation failed.\n");
        return 1;
    }

    // Alternating a, b, a, b, ... so the second-to-last symbol is 'a' (index 0)
    // and the word is accepted. SYM_A = 0, SYM_B = 1.
    for (unsigned long long i = 0; i < TEST_SIZE; i++) {
        test_vector[i] = (nfa_symbol_t)(i % 2ULL);
    }

    double sum = 0;
    for (int i = 0; i < NUM_TESTS; i++) {
        clock_t start = clock();
        accepted = nfa_accepts(test_vector, TEST_SIZE);
        clock_t end = clock();
        sum += (double)(end - start) / CLOCKS_PER_SEC;
    }

    printf("=== C Benchmark ===\n");
    printf("Number of tests    : %d\n", NUM_TESTS);
    printf("Processed Elements : %d\n", TEST_SIZE);
    printf("Accepted           : %s\n", accepted ? "true" : "false");
    printf("Avg Execution Time : %.6lf seconds\n", sum / NUM_TESTS);

    free(test_vector);
    return 0;
}
