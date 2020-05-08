#include <stdint.h>
#include <stdio.h>
#include <assert.h>

#define RSANUMBYTES 4           /* 32 bit key length */
#define RSANUMWORDS (RSANUMBYTES / sizeof(uint32_t))

typedef struct RSAPublicKey {
    int len;                  /* Length of n[] in number of uint32_t */
    uint32_t n0inv;           /* -1 / n[0] mod 2^32 */
    uint32_t n[RSANUMWORDS];  /* modulus as little endian array */
    uint32_t rr[RSANUMWORDS]; /* R^2 as little endian array */
    int exponent;             /* 3 or 65537 */
} RSAPublicKey;

void dump_uint32_array(const char* name, const uint32_t *a, int len)
{
    printf("%s [", name);
    for (int i = 0; i < len; i ++) {
        printf("0x%x, ", a[i]);
    }
    printf("]\n");
}

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
    printf("n: 0x%x\n", key->n[0]);

    uint64_t A = (uint64_t)a * b[0] + c[0]; // A == a * b
    uint32_t d0 = (uint32_t)A * key->n0inv; // d0 == (a * b * key->n0inv) % BASE
    printf("d0 full: 0x%lx\n", A * ((uint64_t) key->n0inv));
    printf("d0: 0x%x\n", d0);

    uint64_t B = (uint64_t)d0 * key->n[0] + (uint32_t)A; // B == (a * b * key->n0inv) % BASE * key->n + lower(A)

    printf("A: 0x%lx\n", A);
    printf("B: 0x%lx\n", B);

    // (a * b + d_0 * key.n) == (uh64(B) + uh64(A)) * BASE < key->n * BASE

    int i;

    for (i = 1; i < key->len; ++i) {
        A = (A >> 32) + (uint64_t)a * b[i] + c[i];
        B = (B >> 32) + (uint64_t)d0 * key->n[i] + (uint32_t)A;
        c[i - 1] = (uint32_t)B;
    }

    printf("A: 0x%lx\n", A >> 32);
    printf("B: 0x%lx\n", B >> 32);

    uint64_t S = (A >> 32) + (B >> 32);
    printf("S: 0x%lx\n", S);
    assert(S < key->n[0]);

    c[i - 1] = (uint32_t)S;

    if (S >> 32) {
        printf("mont subtraction\n");
        subM(key, c);
    }

    if (c[0] > key->n[0]) {
        printf("result larger than key.n\n");
    } else {
        printf("result not larger than key.n\n");
    }
}

/* montgomery c[] = a[] * b[] / R % mod */
void montMul(const RSAPublicKey *key,
                    uint32_t* c,
                    const uint32_t* a,
                    const uint32_t* b) {
    dump_uint32_array("input a", a, 1);
    dump_uint32_array("input b", b, 1);

    int i;
    for (i = 0; i < key->len; ++i) {
        c[i] = 0;
    }
    for (i = 0; i < key->len; ++i) {
        montMulAdd(key, c, a[i], b);
    }
    dump_uint32_array("output c", c, 1);
    printf("\n");
}

/* In-place public exponentiation.
** Input and output big-endian byte array in inout.
*/
void modpow3(const RSAPublicKey *key, uint32_t* a) {
    uint32_t aR[RSANUMWORDS];
    uint32_t aaR[RSANUMWORDS];
    uint32_t *aaa = aR;  /* Re-use location. */

    montMul(key, aR, a, key->rr);  /* aR = a * RR / R mod M   */
    montMul(key, aaR, aR, aR);     /* aaR = aR * aR / R mod M */
    montMul(key, aaa, aaR, a);     /* aaa = aaR * a / R mod M */

    /* Make sure aaa < mod; aaa is at most 1x mod too large. */
    if (geM(key, aaa)) {
        subM(key, aaa);
        printf("post subtraction\n");
    }

    a[0] = aaa[0];
}

void mont_exp_test(const RSAPublicKey *key) {
    uint32_t a[RSANUMWORDS] = {0x933d77e9};
    modpow3(key, a);
    // dump_uint32_array("a", a, 1);
}

void mont_mul_test_1(const RSAPublicKey *key) {
    uint32_t c[RSANUMWORDS];
    uint32_t a[RSANUMWORDS] = {0x733d77e9}; // a < key.n
    uint32_t b[RSANUMWORDS] = {0x5b8d9507}; // b < key.n

    montMul(key, c, a, b);
    assert(c[0] == 0x87740fa7);
    assert(c[0] > key->n[0]);

    // c == (a * b * R_inv) mod key.n
    // c < 2 * key.n

    dump_uint32_array("c", c, 1);
}

void mont_mul_test_2(const RSAPublicKey *key) {
    uint32_t c[RSANUMWORDS];
    uint32_t a[RSANUMWORDS] = {0x775b4135}; // a > key.n
    uint32_t b[RSANUMWORDS] = {0x775b4135}; // b > key.n

    montMul(key, c, a, b);

    // c == (a * b * R_inv) mod key.n
    // c < 2 * key.n

    dump_uint32_array("c", c, 1);
}

int main() {
    RSAPublicKey key;
    
    key.len = RSANUMWORDS;
    key.exponent = 3;

    printf("number of words: %lu\n", RSANUMWORDS);

    key.n[0] = 0x755a9e77;
    // R_inv = 0x3e22aff1 // R_inv * R == 1 mod key.n
    key.n0inv = 0x878b64b9; // key.n0inv * key.n[0] == -1 mod b
    key.rr[0] = 0x2f305830;
    
    // mont_mul_test();
    mont_mul_test_2(&key);
    return 0;
}