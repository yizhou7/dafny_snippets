#include <stdint.h>
#define RSANUMWORDS 8

static void subM(uint32_t *a, const uint32_t* n) {
    int64_t A = 0;

    A += (uint64_t)a[0] - n[0];
    a[0] = (uint32_t)A;
    A >>= 32;

    A += (uint64_t)a[1] - n[1];
    a[1] = (uint32_t)A;
    A >>= 32;

    A += (uint64_t)a[2] - n[2];
    a[2] = (uint32_t)A;
    A >>= 32;

    A += (uint64_t)a[3] - n[3];
    a[3] = (uint32_t)A;
    A >>= 32;

    A += (uint64_t)a[4] - n[4];
    a[4] = (uint32_t)A;
    A >>= 32;

    A += (uint64_t)a[5] - n[5];
    a[5] = (uint32_t)A;
    A >>= 32;

    A += (uint64_t)a[6] - n[6];
    a[6] = (uint32_t)A;
    A >>= 32;

    A += (uint64_t)a[7] - n[7];
    a[7] = (uint32_t)A;
    A >>= 32;
}

// static void montMulAdd(const uint32_t* n,
// 						uint32_t n0inv,
//                    		uint32_t* c,
//                     	const uint32_t a,
// 						const uint32_t* b) {
//     uint64_t A = (uint64_t)a * b[0] + c[0];
//     uint32_t d0 = (uint32_t)A * n0inv;
//     uint64_t B = (uint64_t)d0 * n[0] + (uint32_t)A;
//     int i;

//     for (i = 1; i < RSANUMWORDS; ++i) {
//         A = (A >> 32) + (uint64_t)a * b[i] + c[i];
//         B = (B >> 32) + (uint64_t)d0 * n[i] + (uint32_t)A;
//         c[i - 1] = (uint32_t)B;
//     }

//     A = (A >> 32) + (B >> 32);

//     c[i - 1] = (uint32_t)A;

//     // if (A >> 32) {
//     //     subM(key, c);
//     // }
// }
