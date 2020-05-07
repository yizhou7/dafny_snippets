#include <stdint.h>
#include <stdio.h>

#define RSANUMBYTES 4           /* 32 bit key length */
#define RSANUMWORDS (RSANUMBYTES / sizeof(uint32_t))

typedef struct RSAPublicKey {
    int len;                  /* Length of n[] in number of uint32_t */
    uint32_t n0inv;           /* -1 / n[0] mod 2^32 */
    uint32_t n[RSANUMWORDS];  /* modulus as little endian array */
    // uint32_t rr[RSANUMWORDS]; /* R^2 as little endian array */
    int exponent;             /* 3 or 65537 */
} RSAPublicKey;

/* a[] -= mod */
static void subM(const RSAPublicKey *key, uint32_t *a) {
    int64_t A = 0;
    int i;
    for (i = 0; i < key->len; ++i) {
        A += (uint64_t)a[i] - key->n[i];
        a[i] = (uint32_t)A;
        A >>= 32;
    }
}

/* return a[] >= mod */
int geM(const RSAPublicKey *key, const uint32_t *a) {
    int i;
    for (i = key->len; i;) {
        --i;
        if (a[i] < key->n[i]) return 0;
        if (a[i] > key->n[i]) return 1;
    }
    return 1;  /* equal */
}

/* montgomery c[] += a * b[] / R % mod */
void montMulAdd(const RSAPublicKey *key,
                       uint32_t* c,
                       const uint32_t a,
                       const uint32_t* b) {
    uint64_t A = (uint64_t)a * b[0] + c[0];
    uint32_t d0 = (uint32_t)A * key->n0inv;
    uint64_t B = (uint64_t)d0 * key->n[0] + (uint32_t)A;
    int i;

    for (i = 1; i < key->len; ++i) {
        A = (A >> 32) + (uint64_t)a * b[i] + c[i];
        B = (B >> 32) + (uint64_t)d0 * key->n[i] + (uint32_t)A;
        c[i - 1] = (uint32_t)B;
    }

    A = (A >> 32) + (B >> 32);

    c[i - 1] = (uint32_t)A;

    if (A >> 32) {
        printf("subtraction!\n");
        subM(key, c);
    }
}

/* montgomery c[] = a[] * b[] / R % mod */
void montMul(const RSAPublicKey *key,
                    uint32_t* c,
                    const uint32_t* a,
                    const uint32_t* b) {
    int i;
    for (i = 0; i < key->len; ++i) {
        c[i] = 0;
    }
    for (i = 0; i < key->len; ++i) {
        montMulAdd(key, c, a[i], b);
    }
}

// /* In-place public exponentiation.
// ** Input and output big-endian byte array in inout.
// */
// void modpow3(const RSAPublicKey *key, uint8_t* inout) {
//     uint32_t a[RSANUMWORDS];
//     uint32_t aR[RSANUMWORDS];
//     uint32_t aaR[RSANUMWORDS];
//     uint32_t *aaa = aR;  /* Re-use location. */
//     int i;

//     montMul(key, aR, a, key->rr);  /* aR = a * RR / R mod M   */
//     montMul(key, aaR, aR, aR);     /* aaR = aR * aR / R mod M */
//     montMul(key, aaa, aaR, a);     /* aaa = aaR * a / R mod M */

//     /* Make sure aaa < mod; aaa is at most 1x mod too large. */
//     if (geM(key, aaa)) {
//         subM(key, aaa);
//     }
// }

void dump_uint32_array(const uint32_t *a, int len)
{
    printf("[");
    for (int i = 0; i < len; i ++) {
        printf("%x, ", a[i]);
    }
    printf("]\n");
}

int main() {
    RSAPublicKey key;
    key.len = RSANUMWORDS;
    key.exponent = 3;

    printf("number of words: %lu\n", RSANUMWORDS);

    key.n0inv = 0x878b64b9; // key.n0inv * key.n[0] == -1 mod b
    key.n[0] = 0x755a9e77;
    // R_inv = 0x3e22aff1 // R_inv * R == 1 mod key.n

    uint32_t c[RSANUMWORDS];

    uint32_t a[RSANUMWORDS] = {1933408233};
    uint32_t b[RSANUMWORDS] = {1536005383};

    montMul(&key, c, a, b);

    dump_uint32_array(c, 1);
    // modpow3(key, buf);
    return 1;
}