// ccomp -O3 -o vending_perf examples/perftests/vending.c examples/vending.c -I examples/
/*
=== C Benchmark ===
Processed Elements : 1000000
Final State        : YELLOW
Execution Time     : 0.005226 seconds
=== OCaml Benchmark ===
Processed Elements : 100
Trace              : --BACK 15-VEND-BACK 10-VEND-BACK 10-VEND-BACK 10-VEND-BACK 10-VEND-BACK 10-VEND-BACK 10-VEND-BACK 10-VEND-BACK 10-VEND-BACK 10-VEND-BACK 10-VEND-BACK 10-VEND-BACK 10-VEND-BACK 10-VEND-BACK 10-VEND-BACK 10-VEND-BACK 10-VEND-BACK 10-VEND-BACK 10-VEND-BACK 10-VEND-BACK 10-VEND-BACK 10-VEND-BACK 10-VEND-BACK 10-VEND-BACK 10-
Execution Time     : 0.000143 seconds
*/
/*
# lscpu | grep -E 'Model name|Architecture|CPU\(s\):|cache'
Architecture:                            x86_64
CPU(s):                                  22
Model name:                              Intel(R) Core(TM) Ultra 7 155H
L1d cache:                               528 KiB (11 instances)
L1i cache:                               704 KiB (11 instances)
L2 cache:                                22 MiB (11 instances)
L3 cache:                                24 MiB (1 instance)
NUMA node0 CPU(s):                       0-21
*/

#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include "vending.h"

#define TEST_SIZE 1000000

const char* output_to_string(moore_output_t out) {
    switch(out) {
        case OUT_RED:        return "RED";
        case OUT_GREEN:      return "GREEN";
        case OUT_YELLOW:     return "YELLOW";
        case OUT_RED_YELLOW: return "RED+YELLOW";
        default:             return "UNKNOWN";
    }
}

int main(void)
{
    moore_word_t test_vector = malloc(sizeof(moore_symbol_t) * TEST_SIZE);
    if (!test_vector) {
        fprintf(stderr, "Memory allocation failed.\n");
        return 1;
    }

    for (unsigned long long i = 0; i < TEST_SIZE; i++) {
        test_vector[i] = (moore_symbol_t)((i % 4ULL) == 0ULL ? SYM_R : SYM_T);
    }

    clock_t start = clock();
    moore_output_t final_output = moore_run_output(test_vector, TEST_SIZE);
    clock_t end = clock();

    double elapsed = (double)(end - start) / CLOCKS_PER_SEC;

    printf("=== C Benchmark ===\n");
    printf("Processed Elements : %d\n", TEST_SIZE);
    printf("Final State        : %s\n", output_to_string(final_output));
    printf("Execution Time     : %.6f seconds\n", elapsed);

    free(test_vector);
    return 0;
}
