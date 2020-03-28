include "NativeTypes.dfy"
include "Powers.dfy"
include "Congruences.dfy"
include "SeqInt.dfy"

module RSAE3v2 {
    import opened NativeTypes
    import opened Powers
    import opened Congruences
    import opened SeqInt

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
        returns (A'': seq<uint32>)
    {
        assume false;

        var u_i_ := ((A[0] as int + x_i as int * y[0] as int) * m' as int) % BASE; 
        var u_i := u_i_ as uint32;

        var i := 0;

        var product_1 :uint64;
        var product_2 :uint64;

        var A' := zero_seq_int(n + 1);

        while i < n
        {
            product_1 := uh64(product_1) as uint64 + y[i] as uint64 * x_i as uint64 + A[i] as uint64;
            product_2 := uh64(product_2) as uint64 + u_i as uint64 * m[i] as uint64 + lh64(product_1) as uint64;

            i := i + 1;
        }

        A' := A'[1..];
    }

    method magic_mul(A: seq<uint32>, b: uint32, n: nat)
        returns (P: seq<uint32>)
        requires n != 0;
        requires |A| == n;
        ensures |P| == n + 1;
    {
        var temp := new uint32[n + 1];
        temp[0] := 0;
        P := temp[..];

        assert P[0] == 0;

        var i := 0;
        var c :uint32 := 0;

        while i < n 
            decreases n - i;
            invariant |A| == n;
            invariant |P| == n + 1;
            invariant i < |P|;
        {
            var product :uint64 := A[i] as uint64 * b as uint64 + c as uint64;
            var lower, upper := split64(product);

            P := P[i := lower];
            i := i + 1;
            c := upper;
        }
    
        P := P[n := c];
    }
}