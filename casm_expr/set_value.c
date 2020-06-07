#include <stdint.h>

void subM(uint32_t *a, const uint32_t* n) {
    int64_t A = 0;
    A += (uint64_t)a[0] - n[0];
    a[0] = (uint32_t)A;
}