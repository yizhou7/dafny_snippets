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

    lemma compact_mont_mul_divisible_lemma(p_1: nat, p_2: nat, x_i: nat, y_0: nat, a_0: nat, u_i: nat, m': nat, m_0: nat)
        requires cong(m' * m_0, -1, BASE);
        requires p_1 <= UINT64_MAX as nat;
        requires p_1 == x_i * y_0 + a_0;
        requires u_i == (lh64(p_1 as uint64) as nat * m') % BASE;
        requires p_2 == u_i * m_0 + lh64(p_1 as uint64) as nat;
        ensures cong(p_2, 0, BASE);
    {
        assert lh64(p_1 as uint64) as nat == p_1 % BASE by {
            split64_lemma(p_1 as uint64);
        }

        calc ==> {
            cong(m' * m_0, -1, BASE);
            {
                mont_mul_div_aux_lemma_1(y_0, x_i, m_0, a_0, m');
            }
            cong(y_0 * x_i + a_0 + m_0 * (((a_0 + x_i * y_0) * m') % BASE) , 0, BASE);
            {
                assert p_1 == x_i * y_0 + a_0;
            }
            cong(p_1 + m_0 * ((p_1 * m') % BASE) , 0, BASE);
            {
                cong_mod_lemma(p_1, BASE);
                assert cong(p_1 % BASE, p_1, BASE);
                cong_mul_lemma_1(p_1 % BASE, p_1, m', BASE);
                assert cong((p_1 % BASE) * m', p_1 * m', BASE);
                reveal cong();
                assert (p_1 % BASE * m') % BASE == (p_1 * m') % BASE;
                assert u_i == (p_1 * m') % BASE;
            }
            cong(p_1 + m_0 * u_i , 0, BASE);
            {
                cong_mod_lemma(p_1, BASE);
                assert cong(p_1 % BASE, p_1, BASE);
                cong_add_lemma_1(p_1 % BASE, p_1,  m_0 * u_i, BASE); 
                assert cong(p_1 % BASE + m_0 * u_i, p_1 + m_0 * u_i, BASE);
                cong_trans_lemma(p_1 % BASE + m_0 * u_i, p_1 + m_0 * u_i, 0, BASE);
            }
            cong(p_1 % BASE + m_0 * u_i , 0, BASE);
            cong(p_2, 0, BASE);
        }
    }

    lemma cmma_invarint_aux_lemma_1(m: seq<uint32>,
        A: seq<uint32>, 
        x_i: uint32,
        y: seq<uint32>,
        n: nat,
        p_1: uint64,
        p_2: uint64,
        u_i: uint32)

        requires |m| == |A| == |y| == n > 1;
        requires p_1 as int == x_i as int * y[0] as int  + A[0] as int;
        requires p_2 as int == u_i as int * m[0] as int + lh64(p_1) as int;

        ensures x_i as nat * seq_interp(y[..1]) + u_i as nat * seq_interp(m[..1]) + seq_interp(A[..1]) as nat == 
            uh64(p_2) as int * power(BASE, 1) + uh64(p_1) as int * power(BASE, 1);
    {
        calc == {
            x_i as nat * seq_interp(y[..1]) + u_i as nat * seq_interp(m[..1]) + seq_interp(A[..1]);
            {
                assert power(BASE, 0) == 1 by {
                    reveal power();
                }
            }
            x_i as nat * y[0] as nat + u_i as nat * m[0] as nat + A[0] as nat;
            u_i as nat * m[0] as nat + p_1 as int;
            {
                split64_lemma(p_1);
            }
            u_i as nat * m[0] as nat + lh64(p_1) as int + uh64(p_1) as int * BASE;
            p_2 as int + uh64(p_1) as int * BASE;
            {
                split64_lemma(p_2);
            }
            lh64(p_2) as int + uh64(p_2) as int * BASE + uh64(p_1) as int * BASE;
            {
                assume lh64(p_2) == 0;
            }
            uh64(p_2) as int * BASE + uh64(p_1) as int * BASE;
            {
                reveal power();
            }
            uh64(p_2) as int * power(BASE, 1) + uh64(p_1) as int * power(BASE, 1);
        }
    }

    lemma cmma_invarint_aux_lemma_2(m: seq<uint32>,
        A: seq<uint32>, 
        x_i: uint32,
        y: seq<uint32>,
        n: nat,
        p_1: uint64,
        p_1': uint64,
        p_2: uint64,
        p_2': uint64,
        u_i: uint32,
        j: nat,
        j': nat,
        S: seq<uint32>,
        S': seq<uint32>)
    
        requires |m| == |A| == |y| == n;
        requires 0 < j' < n;
        requires j == j' + 1;
        requires S == S' + [lh64(p_2)];

        requires x_i as nat * seq_interp(y[..j']) + u_i as nat * seq_interp(m[..j']) + seq_interp(A[..j']) == 
                seq_interp(S') + uh64(p_2') as int * BASE + uh64(p_1') as int * BASE;
        requires p_1 as nat == uh64(p_1') as nat  + x_i as nat * y[j'] as nat + A[j'] as nat;
        requires p_2 as nat == uh64(p_2') as nat  + u_i as nat * m[j'] as nat + lh64(p_1) as nat;
    {
        calc == {
            seq_interp(S);
            {
                assume false;
            }
            // seq_interp(S') + ;



        }
        // assert x_i as nat * seq_interp(y[..j']) + u_i as nat * seq_interp(m[..j']) + seq_interp(A[..j']) == 
        //     seq_interp(S') + uh64(p_2') as int * BASE + uh64(p_1') as int * BASE;

        // S := S + [lh64(p_2)];
        // j := j + 1;
    }



/*
    uint64_t p_1 = (uint64_t)x_i * y[0] + A[0];
    uint32_t u_i = (uint32_t)p_1 * m';
    uint64_t p_2 = (uint64_t)u_i * m[0] + (uint32_t)p_1;

    int i;
    for (i = 1; i < len; ++i) {
        p_1 = (p_1 >> 32) + (uint64_t)x_i * y[i] + A[i];
        p_2 = (p_2 >> 32) + (uint64_t)u_i * m[i] + (uint32_t)p_1;
        A[i - 1] = (uint32_t)p_2;
    }
    p_1 = (p_1 >> 32) + (p_2 >> 32);
    A[i - 1] = (uint32_t)p_1;
    if (p_1 >> 32) {
        subM(key, A);
    }
*/
    method compact_mont_mul_add(m: seq<uint32>,
        A: seq<uint32>, 
        x_i: uint32,
        y: seq<uint32>,
        m': uint32,
        n: nat,
        ghost i: nat,
        ghost BASE_INV: nat,
        ghost x: seq<uint32>)

        returns (A': seq<uint32>)

        requires seq_interp(m) != 0;
        requires |m| == |A| == |y| == |x| == n > 1;
        requires i < n;
        requires cong(seq_interp(A), seq_interp(x[..i]) * seq_interp(y) * power(BASE_INV, i), seq_interp(m));
        // ensures cong(seq_interp(A'), seq_interp(x[..i + 1]) * seq_interp(y) * power(BASE_INV, i), seq_interp(m));
    {
        single_digit_mul_lemma(x_i, y[0], A[0]);
        var p_1 :uint64 := x_i as uint64 * y[0] as uint64 + A[0] as uint64;
        var u_i :uint32 := ((lh64(p_1) as nat * m' as nat) % BASE) as uint32;

        single_digit_mul_lemma(u_i, m[0], lh64(p_1));
        var p_2 :uint64 := u_i as uint64 * m[0] as uint64 + lh64(p_1) as uint64;

        assert cong(p_2 as int, 0, BASE) by {
            assume cong(m' as nat* m[0] as nat, -1, BASE);
            compact_mont_mul_divisible_lemma(p_1 as nat, p_2 as nat, x_i as nat, y[0] as nat, A[0] as nat, u_i as nat, m' as nat, m[0] as nat);
        }

        ghost var S := [0];
        A' := zero_seq_int(n);

        var j := 1;

        assert x_i as nat * seq_interp(y[..j]) + u_i as nat * seq_interp(m[..j]) + seq_interp(A[..1]) as nat == 
            uh64(p_2) as int * power(BASE, j) + uh64(p_1) as int * power(BASE, j) by 
        {
            cmma_invarint_aux_lemma_1(m, A, x_i, y, n, p_1, p_2, u_i);
        }

        while j != n
            decreases n - j;
            invariant 0 < j <= n;
        {
            ghost var S', j', p_1', p_2' := S, j, p_1, p_2;

            assume x_i as nat * seq_interp(y[..j]) + u_i as nat * seq_interp(m[..j]) + seq_interp(A[..j]) == 
                seq_interp(S) + uh64(p_2) as int * power(BASE, j) + uh64(p_1) as int * power(BASE, j);

            p_1 := uh64(p_1) as uint64 + x_i as uint64 * y[j] as uint64 + A[j] as uint64;
            p_2 := uh64(p_2) as uint64 + u_i as uint64 * m[j] as uint64 + lh64(p_1) as uint64;
            // A' := A'[j - 1 := lh64(p_2)];

            // assert x_i as nat * seq_interp(y[..j']) + u_i as nat * seq_interp(m[..j']) + seq_interp(A[..j']) == 
            //     seq_interp(S') + uh64(p_2') as int * BASE + uh64(p_1') as int * BASE;

            S := S + [lh64(p_2)];
            j := j + 1;

            // cmma_invarint_aux_lemma_2(m, A, x_i, y, n, p_1, p_1', p_2, p_2', u_i, j, j', S, S');

        }

        assert j == n;
        // assume x_i as nat * seq_interp(y[..n]) + u_i as nat * seq_interp(m[..n]) + seq_interp(A[..n]) == 
        //     seq_interp(S) + uh64(p_2) as int * BASE + uh64(p_1) as int * BASE;

        // calc == {
        //     seq_interp(S) + uh64(p_2) as int * BASE + uh64(p_1) as int * BASE;
        //     {
        //         assume false;
        //     }
        //     x_i as nat * seq_interp(y[..n]) + u_i as nat * seq_interp(m[..n]) + seq_interp(A[..n]);
        //     {
        //         assert seq_interp(y[..n]) == seq_interp(y) by {
        //             assert y == y[..n];
        //         }
        //     }
        //     x_i as nat * seq_interp(y) + u_i as nat * seq_interp(m[..n]) + seq_interp(A[..n]);
        //     {
        //         assert seq_interp(m[..n]) == seq_interp(m) by {
        //             assert m == m[..n];
        //         }
        //     }
        //     x_i as nat * seq_interp(y) + u_i as nat * seq_interp(m) + seq_interp(A[..n]);
        //     {
        //         assert seq_interp(A[..n]) == seq_interp(A) by {
        //             assert A == A[..n];
        //         }
        //     }
        //     x_i as nat * seq_interp(y) + u_i as nat * seq_interp(m) + seq_interp(A);
        // }

        assume false;

        p_1 := uh64(p_1) as uint64 + uh64(p_2) as uint64;
        A' := A'[j - 1 := lh64(p_1)];
        S := S + [lh64(p_1)];

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
            invariant |A| == n;

            invariant cong(seq_interp(A), seq_interp(x[..i]) * seq_interp(y) * power(BASE_INV, i), seq_interp(m));
            invariant seq_interp(A) <= m_val;
            invariant cong(BASE * BASE_INV, 1, seq_interp(m));
        {
            A := compact_mont_mul_add(m, A, x[i], y, m', n, i, BASE_INV, x);
            i := i + 1;
        }
    }
}