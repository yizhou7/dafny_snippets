include "NativeTypes.dfy"
include "Powers.dfy"
include "Congruences.dfy"
include "SeqInt.dfy"
include "RSAE3.dfy"

module RSAE3v2 {
    import opened NativeTypes
    import opened Powers
    import opened Congruences
    import opened SeqInt
    import opened RSAE3

/*
    uint64_t p_1 = (uint64_t)x_i * y[0] + A[0];
    uint32_t u_i = (uint32_t)p_1 * key->n0inv;
    uint64_t p_2 = (uint64_t)u_i * key->n[0] + (uint32_t)p_1;

    int i;
    for (i = 1; i < key->len; ++i) {
        p_1 = (p_1 >> 32) + (uint64_t)x_i * y[i] + A[i];
        p_2 = (p_2 >> 32) + (uint64_t)u_i * key->n[i] + (uint32_t)p_1;
        A[i - 1] = (uint32_t)p_2;
    }
    p_1 = (p_1 >> 32) + (p_2 >> 32);
    A[i - 1] = (uint32_t)p_1;
    if (p_1 >> 32) {
        subM(key, A);
    }
*/
    method compact_mont_mul_add(m: seq<uint32>, A: seq<uint32>, x_i: uint32, y: seq<uint32>, m': uint32, n: nat)
        returns (A': seq<uint32>)
        requires |m| == |A| == |y| == n != 0;
    {

        A' := zero_seq_int(n);

        single_digit_mul_lemma(x_i, y[0], A[0]);
        var p_1 :uint64 := x_i as uint64 * y[0] as uint64 + A[0] as uint64;
        var u_i :uint32 := ((p_1 as int * m' as int) % BASE) as uint32;

        single_digit_mul_lemma(u_i, m[0], lh64(p_1));
        var p_2 :uint64 := u_i as uint64 * m[0] as uint64 + lh64(p_1) as uint64;
        assume false;

        var i := 1;

        while i < n
            // invariant |A'| == 
        {
            p_1 := uh64(p_1) as uint64 + x_i as uint64 * y[i] as uint64 + A[i] as uint64;
            p_2 := uh64(p_2) as uint64 + u_i as uint64 * m[i] as uint64 + lh64(p_1) as uint64;
            A' := A'[i - 1 := lh64(p_2)];
            i := i + 1;
        } 

        p_1 := uh64(p_1) as uint64 + uh64(p_2) as uint64;
        A' := A'[i - 1 := lh64(p_1)];

        if uh64(p_1) != 0 {
            var _, A'' := seq_sub(A', m);
            A' := A'';
        }
    }

    method compact_mont_mul(m: seq<uint32>, x: seq<uint32>, y: seq<uint32>, m': uint32, n: nat, ghost R: int, ghost BASE_INV: nat)
        returns (A: seq<uint32>)

        requires n > 2;
        requires |m| == n && |x| == n && |y| == n;
        requires R == power(BASE, n);
        requires cong(m' as int * seq_interp(m), -1, BASE);
        requires 0 <= seq_interp(x) < seq_interp(m); 
        requires 0 <= seq_interp(y) < seq_interp(m); 
        requires cong(BASE * BASE_INV, 1, seq_interp(m));
        // ensures seq_interp(A) == (seq_interp(x) * seq_interp(y) * power(BASE_INV, n)) % seq_interp(m);
    {
        assume false;

        A  := zero_seq_int(n);
        assert seq_interp(A) == 0;

        ghost var m_val := seq_interp(m);
        ghost var y_val := seq_interp(y);

        var i := 0;
        
        while i < n
            decreases n - i;
            invariant i <= |x|;
            invariant cong(seq_interp(A), seq_interp(x[..i]) * seq_interp(y) * power(BASE_INV, i), seq_interp(m));
            invariant seq_interp(A) < 2 * m_val - 1;
            invariant cong(BASE * BASE_INV, 1, seq_interp(m));
            invariant |A| == n;
        {
            A := compact_mont_mul_add(m, A, x[i], y, m', n);
            i := i + 1;
        }
    }
}