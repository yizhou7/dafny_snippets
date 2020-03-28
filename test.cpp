#include <cstdint>
#include <iostream>
#include <iomanip>
#include <bitset>

using namespace std;

struct RSAPublicKey
{
    uint32_t len;
    uint32_t *n;
    uint32_t n0inv;
};

void print_number(uint32_t *a, uint32_t len)
{
    for (uint32_t i = 0; i < len; i++)
    {
        cout << "[" << setw(5) << a[i] << "] ";
    }
    cout << endl;
}

void subM(const RSAPublicKey *key, uint32_t *a)
{
    uint32_t len = key->len;

    int64_t A = 0;
    int i;
    for (uint32_t i = 0; i < len; ++i)
    {
        A += (uint64_t)a[i] - key->n[i];
        a[i] = (uint32_t)A;
        // cout << (uint32_t)A << " ";
        A >>= 32;
        // cout << A << endl;
    }
    print_number(a, len);
}

// B = 2 ** 32
// R = 2 ** 32
// N = 72639 
// m' = 3837733825 # (m'* N) % B == -1
// R_inv = 64906 # (R * R_inv) % N == 1

uint32_t c[4] = {0};
uint32_t b[4] = {123};
uint32_t n[4] = {72639};

RSAPublicKey key {
    .len = 1,
    .n = n,
    .n0inv = 3837733825,
};

/* montgomery c[] += a * b[] / R % mod */
static void montMulAdd(const RSAPublicKey *key,
                       uint32_t* A,
                       const uint32_t x_i,
                       const uint32_t* y) {
    uint64_t p_1 = (uint64_t)x_i * b[0] + A[0];
    uint32_t u_i = (uint32_t)p_1 * key->n0inv;
    uint64_t p_2 = (uint64_t)u_i * key->n[0] + (uint32_t)p_1;

    int i;
    for (i = 1; i < key->len; ++i) {
        p_1 = (p_1 >> 32) + (uint64_t)x_i * y[i] + c[i];
        p_2 = (p_2 >> 32) + (uint64_t)u_i * key->n[i] + (uint32_t)p_1;
        A[i - 1] = (uint32_t)p_2;
    }
    p_1 = (p_1 >> 32) + (p_2 >> 32);
    A[i - 1] = (uint32_t)p_1;
    if (p_1 >> 32) {
        subM(key, A);
    }
}
/* montgomery c[] = a[] * b[] / R % mod */
static void montMul(const RSAPublicKey *key,
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

int main()
{

}