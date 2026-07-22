// ccomp -O3 -o traffic_perf examples/perftests/traffic.c examples/traffic.c -I examples/
/*
=== OCaml Benchmark ===
Processed Elements : 1000000
Final State        : YELLOW
Execution Time     : 0.197155 seconds
=== C Benchmark ===                  
Processed Elements : 1000000
Final State        : YELLOW
Execution Time     : 0.002738 seconds
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
#include "traffic.h"

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
