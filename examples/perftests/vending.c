// ccomp -O3 -o vending_perf examples/perftests/vending.c examples/vending.c -I examples/
/*
=== C Benchmark ===
Processed Elements : 100
Trace              : --BACK 15-VEND-BACK 10-VEND-BACK 10-VEND-BACK 10-VEND-BACK 10-VEND-BACK 10-VEND-BACK 10-VEND-BACK 10-VEND-BACK 10-VEND-BACK 10-VEND-BACK 10-VEND-BACK 10-VEND-BACK 10-VEND-BACK 10-VEND-BACK 10-VEND-BACK 10-VEND-BACK 10-VEND-BACK 10-VEND-BACK 10-VEND-BACK 10-VEND-BACK 10-VEND-BACK 10-VEND-BACK 10-VEND-BACK 10-VEND-BACK 10-
Execution Time     : 0.000020 seconds
=== OCaml Benchmark ===
Processed Elements : 100
Trace              : --BACK 15-VEND-BACK 10-VEND-BACK 10-VEND-BACK 10-VEND-BACK 10-VEND-BACK 10-VEND-BACK 10-VEND-BACK 10-VEND-BACK 10-VEND-BACK 10-VEND-BACK 10-VEND-BACK 10-VEND-BACK 10-VEND-BACK 10-VEND-BACK 10-VEND-BACK 10-VEND-BACK 10-VEND-BACK 10-VEND-BACK 10-VEND-BACK 10-VEND-BACK 10-VEND-BACK 10-VEND-BACK 10-VEND-BACK 10-VEND-BACK 10-
Execution Time     : 0.000110 seconds
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
#include "vending.h"

#define TEST_SIZE 100

const char* output_to_string(mealy_output_t out) {
    switch (out) {
    case OUT__:       return "-";
    case OUT_VEND:    return "VEND";
    case OUT_VEND_5:  return "VEND+5";
    case OUT_VEND_10: return "VEND+10";
    case OUT_VEND_15: return "VEND+15";
    case OUT_VEND_20: return "VEND+20";
    case OUT_BACK_5:  return "BACK 5";
    case OUT_BACK_10: return "BACK 10";
    case OUT_BACK_15: return "BACK 15";
    case OUT_BACK_20: return "BACK 20";
    case OUT_BACK_25: return "BACK 25";
    default:          return "SINK";
    }
}

int main(void)
{
    mealy_symbol_t *test_vector =
        malloc(sizeof(mealy_symbol_t) * TEST_SIZE);
    mealy_output_t *out =
        malloc(sizeof(mealy_output_t) * TEST_SIZE);
    if (!test_vector || !out) {
        fprintf(stderr, "Memory allocation failed.\n");
        return 1;
    }

    for (unsigned long long i = 0; i < TEST_SIZE; i++) {
        switch (i % 4ULL) {
        case 0: test_vector[i] = SYM_N; break;
        case 1: test_vector[i] = SYM_D; break;
        case 2: test_vector[i] = SYM_R; break;
        default: test_vector[i] = SYM_Q; break;
        }
    }

    clock_t start = clock();
    run(test_vector, TEST_SIZE, out);
    clock_t end = clock();

    double elapsed = (double)(end - start) / CLOCKS_PER_SEC;

    printf("=== C Benchmark ===\n");
    printf("Processed Elements : %d\n", TEST_SIZE);
    printf("Trace              : ");
    for (unsigned long long i = 0; i < TEST_SIZE; i++)
        printf("%s", output_to_string(out[i]));
    printf("\n");
    printf("Execution Time     : %.6f seconds\n", elapsed);

    free(test_vector);
    free(out);
    return 0;
}
