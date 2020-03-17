include "NativeTypes.dfy"
include "Powers.dfy"
include "Congruences.dfy"

module SeqInt {
    import opened NativeTypes
    import opened Powers
    import opened Congruences

    const BASE :int := UINT32_MAX as int + 1;

    function method reinterpret_cast(a: int64) : uint64

    // |A[..n]| == n, interp A[..n] as an int 
    function interp(A: seq<uint32>, n: nat) : nat
        decreases n;
        requires 0 <= n <= |A|;
    {
        if n == 0 then 0
        else word_interp(A, n - 1) + interp(A, n - 1)
    }

    function R(n: nat) : nat
        ensures R(n) != 0;
    {
        reveal power();
        power(BASE, n)
    }

    function word_interp(A: seq<uint32>, i: nat) : nat
        requires i < |A|;
    {
        A[i] as nat * postional_weight(i)
    }

    function postional_weight(i: nat) : nat
    {
        power(BASE, i) as nat
    }

    lemma {:induction i} word_interp_upper_bound_lemma(A: seq<uint32>, i: nat)
        requires i < |A|;
        ensures word_interp(A, i) <= power(BASE, i + 1) - power(BASE, i);
    {
        assert A[i] as int <= BASE;
        calc ==> {
            A[i] as int <= BASE;
            A[i] as int * postional_weight(i) <= (BASE - 1) * postional_weight(i);
            {
                assert word_interp(A, i) == A[i] as int * postional_weight(i);
            }
             word_interp(A, i) <= (BASE - 1) * postional_weight(i);
             word_interp(A, i) <= (BASE - 1) * power(BASE, i);
             word_interp(A, i) <= BASE * power(BASE, i) - power(BASE, i);
             {
                power_add_one_lemma(BASE, i);
             }
             word_interp(A, i) <= power(BASE, i + 1) - power(BASE, i);
        }
    }

    function seq_interp(A: seq<uint32>) : nat
    {
        interp(A, |A|)
    }

    lemma {:induction A} seq_interp_upper_bound_lemma(A: seq<uint32>, n: nat)
        requires |A| == n != 0;
        ensures seq_interp(A) < R(n);
    {
        if |A| == 1 {
            reveal power();
        } else {
            ghost var A' := A[..(|A| - 1)];

            calc ==> {
                seq_interp(A) == word_interp(A, |A| - 1) + interp(A, |A| - 1);
                {
                    assert seq_interp(A') == interp(A, |A| - 1) by {
                        prefix_sum_lemma(A, A', |A| - 1);
                    }   
                }
                seq_interp(A) == word_interp(A, |A| - 1) + seq_interp(A');
                {
                    assert seq_interp(A') < power(BASE, |A'|);
                }
                seq_interp(A) < word_interp(A, |A| - 1) + power(BASE, |A'|);
                {
                    assert word_interp(A, |A| - 1) <= power(BASE, |A|) - power(BASE, |A| - 1) by {
                        word_interp_upper_bound_lemma(A, |A| - 1);
                    }
                }
                seq_interp(A) < power(BASE, |A|) - power(BASE, |A| - 1) + power(BASE, |A'|);
                seq_interp(A) < power(BASE, |A|);
            }
        }
    }

    lemma postional_shift_lemma(i: int)
        requires i > 0;
        ensures postional_weight(i - 1) * BASE == postional_weight(i);
    {
        calc == {
            postional_weight(i - 1) * BASE;
            ==
            power(BASE, i - 1) * BASE;
            {
                power_add_one_lemma(BASE, i - 1);
            }
            power(BASE, i);
            ==
            postional_weight(i);
        }
    }

    lemma {:induction i} prefix_sum_lemma(S: seq<uint32>, S': seq<uint32>, i: nat)
        requires 0 <= i <= |S| && 0 <= i <= |S'|;
        requires S[..i] == S'[..i];
        ensures interp(S, i) == interp(S', i);
    {
        assert true;
    }

    method seq_add_impl(A: seq<uint32>, B: seq<uint32>, n: nat) returns (c: uint2, S:seq<uint32>)
        requires |A| == |B| == n;
        ensures |S| == n;
        ensures seq_interp(A) + seq_interp(B) == seq_interp(S) + c as int * postional_weight(n);
        ensures n != 0 ==> cong(S[0] as int, A[0] as int + B[0] as int, BASE);
    {
        var temp := new uint32[|A|];
        c, S := 0, temp[..];

        var i: nat := 0;
        ghost var S_old;

        while i < n
            invariant |S| == |A|;
            invariant 0 <= i <= |A|;
            decreases |A| - i;
            invariant interp(A, i) + interp(B, i) == interp(S, i) + c as int * postional_weight(i);
            invariant i > 0 ==> cong(S[0] as int, A[0] as int + B[0] as int, BASE);
        {
            ghost var c_old, i_old: int := c, i;
            assert interp(A, i_old) + interp(B, i_old) == interp(S, i_old) + c_old as int * postional_weight(i_old);

            var sum: uint64 := A[i] as uint64 + B[i] as uint64 + c as uint64;
            var masked := and64(sum, UINT32_MAX as uint64) as uint32;
            assume masked as int + BASE == sum as int;

            S_old := S;
            ghost var prefix_sum := interp(S_old, i);
            S := S[i := masked];

            if i == 0 {
                assert cong(S[0] as int, A[0] as int + B[0] as int, BASE);
            } else {
                assert S[0] == S_old[0];
            }

            assert prefix_sum == interp(S, i_old) by {
                prefix_sum_lemma(S, S_old, i_old);
                assert interp(S, i_old) == interp(S_old, i_old);
            }

            i := i + 1;

            assert interp(A, i_old) + interp(B, i_old) == interp(S, i_old) + c_old as int * postional_weight(i_old);
            assert interp(S, i) == masked as int * postional_weight(i_old) + interp(S, i_old);
            assert interp(B, i) == B[i - 1] as int * postional_weight(i - 1) + interp(B, i - 1);
            assert interp(A, i) == A[i - 1] as int * postional_weight(i - 1) + interp(A, i - 1);

            calc == {
                interp(A, i) + interp(B, i);
                ==
                A[i - 1] as int * postional_weight(i - 1) + interp(A, i_old) +
                B[i - 1] as int * postional_weight(i - 1) + interp(B, i_old);
                ==
                A[i - 1] as int * postional_weight(i - 1) + 
                B[i - 1] as int * postional_weight(i - 1) +
                interp(S, i_old) + c_old as int * postional_weight(i_old);
                ==
                postional_weight(i - 1) * (A[i - 1] as int + B[i - 1] as int + c_old as int) +
                interp(S, i_old);
                ==
                postional_weight(i - 1) * (sum as int) + interp(S, i_old);
            }

            if sum > UINT32_MAX as uint64 {
                c := 1;
                calc == {
                    postional_weight(i - 1) * (sum as int) + interp(S, i_old);
                    postional_weight(i - 1) * masked as int + postional_weight(i - 1) * BASE + interp(S, i_old);
                    {
                        postional_shift_lemma(i);
                    }
                    postional_weight(i - 1) * masked as int + postional_weight(i) + interp(S, i_old);
                }
            } else {
                c := 0;
            }
            assert interp(A, i) + interp(B, i) == interp(S, i) + c as int * postional_weight(i);
        }
    }

    method seq_add(A: seq<uint32>, B: seq<uint32>, n: nat) returns (S: seq<uint32>)
        requires |A| == |B| == n;
        ensures |S| == n;
        ensures cong(seq_interp(A) + seq_interp(B), seq_interp(S), power(BASE, n));
        ensures n != 0 ==> cong(S[0] as int, A[0] as int + B[0] as int, BASE);
    {
        var c;
        c, S := seq_add_impl(A, B, n);

        if c == 0 {
            assert cong(seq_interp(A) + seq_interp(B), seq_interp(S), power(BASE, n)) by {
                assert seq_interp(A) + seq_interp(B) == seq_interp(S);
                reveal cong();
            }
        } else {
            assert cong(seq_interp(A) + seq_interp(B), seq_interp(S), power(BASE, n)) by {
                assert cong(seq_interp(A) + seq_interp(B), seq_interp(S) + postional_weight(n), power(BASE, n)) by {
                    assert seq_interp(A) + seq_interp(B) == seq_interp(S) + postional_weight(n);
                    reveal cong();
                }
                assert cong(seq_interp(S) + power(BASE, n), seq_interp(S), power(BASE, n)) by {
                    cong_add_lemma_3(seq_interp(S), power(BASE, n), power(BASE, n));
                    reveal cong();
                }
                cong_trans_lemma(seq_interp(A) + seq_interp(B), seq_interp(S) + power(BASE, n), seq_interp(S), power(BASE, n));
            }
        }
    }

    method seq_add_c(A: seq<uint32>, B: seq<uint32>, n: nat) returns (S: seq<uint32>)
        requires |A| == |B| == n;
        ensures |S| == n + 1;
        ensures seq_interp(A) + seq_interp(B) == seq_interp(S)
        ensures n != 0 ==> cong(S[0] as int, A[0] as int + B[0] as int, BASE);
    {
        var c, S' := seq_add_impl(A, B, n);
        S := S' + [c as uint32];
        calc == {
            seq_interp(A) + seq_interp(B);
            seq_interp(S') + c as int * postional_weight(n);
            seq_interp(S') + word_interp(S, n);
            interp(S', n) + word_interp(S, n);
            {
                prefix_sum_lemma(S, S', n);
            }
            interp(S, n) + word_interp(S, n);
            seq_interp(S);
        }
    }

    lemma {:induction m} zero_extend_lemma(A: seq<uint32>, n: nat, A': seq<uint32>, m: nat)
        requires |A| == n && |A'| == m;
        requires n < m;
        requires forall i :: 0 <= i < n ==> A[i] == A'[i];
        requires forall i :: n <= i < m ==> A'[i] == 0;
        ensures seq_interp(A') == seq_interp(A); 
    {
        if m != n {
            assume false;
        }
    }

    method seq_zero_extend(A: seq<uint32>, n: nat, m: nat) returns (A': seq<uint32>)
        requires |A| == n;
        requires m > n;
        ensures |A'| == m;
        ensures seq_interp(A') == seq_interp(A); 
        ensures forall i :: 0 <= i < n ==> A[i] == A'[i];
        ensures forall i :: n <= i < m ==> A'[i] == 0;
    {
        var temp := new uint32[m];
        var i := 0;

        while i < m 
            decreases m - i;
            invariant forall j:: 0 <= j < i < n ==> temp[j] == A[j];
            invariant forall j:: n <=  j < i < m ==> temp[j] == 0;
        {
            if i < n {
                temp[i] := A[i];
            } else {
                temp[i] := 0;
            }
            i := i + 1;
        }

        assume false;
        A' := temp[..];
    }

    method seq_sub(A: seq<uint32>, B: seq<uint32>) returns (b: uint2, S:seq<uint32>)
        requires |A| == |B|;
        ensures seq_interp(A) - seq_interp(B) == seq_interp(S) - b as int * postional_weight(|A|);
    {
        var temp := new uint32[|A|];
        b, S := 0, temp[..];

        var i: nat := 0;

        while i < |A|
            invariant |S| == |A|;
            invariant 0 <= i <= |A|;
            decreases |A| - i;
            invariant interp(A, i) - interp(B, i) == interp(S, i) - b as int * postional_weight(i);
        {
            var b_old, i_old: int := b, i;
            assert interp(A, i_old) - interp(B, i_old) == interp(S, i_old) - b_old as int * postional_weight(i_old);

            var diff: int64 := A[i] as int64 - B[i] as int64 - b as int64;
            var masked := and64(reinterpret_cast(diff), UINT32_MAX as uint64) as uint32;

            assume diff < 0 ==> masked as int == diff as int + BASE as int;
            assume diff >= 0 ==> masked as int == diff as int;

            ghost var S_old := S;
            ghost var prefix_sum := interp(S_old, i);
            S := S[i := masked];

            assert prefix_sum == interp(S, i_old) by {
                prefix_sum_lemma(S, S_old, i_old);
                assert interp(S, i_old) == interp(S_old, i_old);
            }

            i := i + 1;

            assert interp(A, i_old) - interp(B, i_old) == interp(S, i_old) - b_old as int * postional_weight(i_old);
            assert interp(S, i) == masked as int * postional_weight(i_old) + interp(S, i_old);
            assert interp(B, i) == B[i - 1] as int * postional_weight(i - 1) + interp(B, i - 1);
            assert interp(A, i) == A[i - 1] as int * postional_weight(i - 1) + interp(A, i - 1);

            calc == {
                interp(A, i) - interp(B, i);
                ==
                A[i - 1] as int * postional_weight(i - 1) + interp(A, i_old) -
                B[i - 1] as int * postional_weight(i - 1) - interp(B, i_old);
                ==
                A[i - 1] as int * postional_weight(i - 1) - 
                B[i - 1] as int * postional_weight(i - 1) +
                interp(S, i_old) - b_old as int * postional_weight(i_old);
                ==
                postional_weight(i - 1) * (A[i - 1] as int - B[i - 1] as int - b_old as int) +
                interp(S, i_old);
            }

            if diff < 0 {
                b := 1;
                calc == {
                    postional_weight(i - 1) * (diff as int) + interp(S, i_old);
                    postional_weight(i - 1) * masked as int - postional_weight(i - 1) * BASE + interp(S, i_old);
                    {
                        postional_shift_lemma(i);
                    }
                    postional_weight(i - 1) * masked as int - postional_weight(i) + interp(S, i_old);
                }
            } else {                
                b := 0;
                assert interp(A, i) - interp(B, i) == interp(S, i);
            }
            assert interp(A, i) - interp(B, i) == interp(S, i) - b as int * postional_weight(i);
        }
    }

    method seq_geq(A: seq<uint32>, B: seq<uint32>) returns (x: bool)
        requires |A| == |B| as int;
        // ensures x == (seq_interp(A) >= seq_interp(B));
    {
        x := false;
        var i := |A|;

        while i != 0
            decreases i;
            invariant 0 <= i <= |A|;
            invariant forall j :: i <= j < |A| ==> A[j] == B[j];
        {
            var i' := i - 1;

            if A[i'] < B[i'] {
                return false;
            }
            if A[i'] > B[i'] {
                return true;
            }

            var j :| i' <= j < |A|;

            assert A[j] == B[j] by {
                if i <= j < |A| {
                    assert forall j :: i < j < |A| ==> A[j] == B[j];
                } else {
                    assert j == i';
                    assert A[i'] == B[i'];
                }
            }
    
            i := i';
        }

        return true;
    }

    lemma {:induction A} lsw_mod_lemma(A: seq<uint32>)
        ensures |A| != 0 ==> (seq_interp(A) % BASE == A[0] as int);
    {
        if |A| == 0 || |A| == 1 {
            reveal power();
        } else {
            ghost var n := |A|;
            assert n >= 1;
            ghost var A' := A[..n - 1];

            calc ==> {
                seq_interp(A') % BASE == A'[0] as int;
                {
                    cong_residual_lemma(seq_interp(A'), A[0] as int, BASE);
                }
                cong(seq_interp(A'), A[0] as int, BASE);
                {
                    assert seq_interp(A') == interp(A', n - 1);
                }
                cong(interp(A', n - 1), A[0] as int, BASE);
                {
                    assert interp(A, n - 1) == interp(A', n - 1) by {
                        prefix_sum_lemma(A, A', n - 1);
                    }
                }
                cong(interp(A, n - 1), A[0] as int, BASE);
                {
                    assert cong(word_interp(A, n - 1), 0, BASE) by {
                        assert power(BASE, n - 1) % BASE == 0 by {
                            power_mod_lemma(BASE, n - 1);
                        }
                        calc ==> {
                            power(BASE, n - 1) % BASE == 0;
                            {
                                cong_residual_lemma(power(BASE, n - 1), 0, BASE);
                            }
                            cong(power(BASE, n - 1), 0, BASE);
                            {
                                cong_mul_lemma_1(power(BASE, n - 1), 0, A[n - 1] as int, BASE);
                            }
                            cong(power(BASE, n - 1) * A[n - 1] as int, 0, BASE);
                            {
                                assert word_interp(A, n - 1) == A[n - 1] as int * power(BASE, n - 1);
                            }
                            cong(word_interp(A, n - 1), 0, BASE);
                        }
                    }
                    cong_add_lemma_2(interp(A, n - 1), A[0] as int, word_interp(A, n - 1), 0, BASE);
                }
                cong(interp(A, n - 1) + word_interp(A, n - 1), A[0] as int, BASE);
                cong(seq_interp(A), A[0] as int, BASE);
            }

            assert cong( seq_interp(A), A[0] as int, BASE);
            assert A[0] as int < BASE;
            cong_residual_lemma(seq_interp(A), A[0] as nat, BASE);
        }
    }

    lemma lsw_inverse_lemma(m: seq<uint32>, m': uint32)
        requires |m| != 0;
        requires cong(m' as int * seq_interp(m), -1, BASE);
        ensures cong(m' as int * m[0] as int, -1, BASE);
    {
        assert cong(seq_interp(m), seq_interp(m) % BASE, BASE) by {
            cong_mod_lemma(seq_interp(m), BASE);
            reveal cong();
        }

        calc ==> {
            cong(seq_interp(m), seq_interp(m) % BASE, BASE);
            {
                assert (seq_interp(m) % BASE == m[0] as int) by {
                    lsw_mod_lemma(m);
                }
            }
            cong(seq_interp(m),  m[0] as int, BASE);
            {
                cong_mul_lemma_1(seq_interp(m), m[0] as int, m' as int, BASE);
            }
            cong(seq_interp(m) * m' as int,  m[0] as int * m' as int, BASE);
            {
                reveal cong();
            }
            cong(m[0] as int * m' as int, -1, BASE);
        }
    }

    lemma {:induction T} seq_div_base_lemma(T: seq<uint32>, n: nat)
        requires |T| == n > 0;
        requires cong(T[0] as int, 0, BASE);
        ensures seq_interp(T) % BASE == 0;
        ensures seq_interp(T) / BASE == seq_interp(T[1..]);
    {
        if n == 1 {
            reveal cong();
        } else {
            var T' := T[..n-1];

            calc =={
                seq_interp(T); 
                (T[n-1] as int * postional_weight(n-1) + interp(T, n - 1));
                {
                    prefix_sum_lemma(T, T', n - 1);
                }
                (T[n-1] as int * postional_weight(n-1) + interp(T', n - 1));
                (T[n-1] as int * postional_weight(n-1) + seq_interp(T'));
                (T[n-1] as int * power(BASE, n-1) + seq_interp(T'));
            }

            assert A1: power(BASE, n-1) % BASE == 0 by {
                power_mod_lemma(BASE, n-1);
            }

            assert A2: seq_interp(T') % BASE == 0 by {
                seq_div_base_lemma(T', n - 1);
            }

            assert seq_interp(T) % BASE == 0 by {
                reveal A1, A2;
                assert (T[n-1] as int * power(BASE, n-1)) % BASE == 0 by {
                    mod_mul_lemma(T[n-1] as int, power(BASE, n-1), BASE);
                }
                assert (T[n-1] as int * power(BASE, n-1) + seq_interp(T')) % BASE == 0;
            }

            calc == {
                seq_interp(T) / BASE;
                (T[n-1] as int * power(BASE, n-1) + seq_interp(T')) / BASE;
                {
                    reveal A1, A2;
                }
                T[n-1] as int * (power(BASE, n-1) / BASE) + seq_interp(T') / BASE;
                {
                    assert seq_interp(T') / BASE == seq_interp(T'[1..]) by {
                        seq_div_base_lemma(T', n - 1);
                    }
                }
                T[n-1] as int * (power(BASE, n-1) / BASE) + seq_interp(T'[1..]);
                {
                    assert  power(BASE, n-1) / BASE ==  power(BASE, n-2) by {
                        power_sub_one_lemma(BASE, n-1);
                    }
                }
                T[n-1] as int * power(BASE, n-2) + seq_interp(T'[1..]);
                T[n-1] as int * power(BASE, n-2) + seq_interp(T[1..n-1]);
                {
                    assert seq_interp(T[1..n-1]) == interp(T[1..n-1], n - 2);
                }
                T[n-1] as int * power(BASE, n-2) + interp(T[1..n-1], n - 2);
                {
                    assert interp(T[1..n-1], n - 2) == interp(T[1..], n -2) by {
                        prefix_sum_lemma(T[1..n-1], T[1..], n - 2);
                    }
                }
                T[n-1] as int * power(BASE, n-2) + interp(T[1..], n -2);
                word_interp(T[1..], n - 2) + interp(T[1..], n - 2);
                seq_interp(T[1..]);
            }
        }
    }

    lemma msw_zero_lemma(T: seq<uint32>, n: nat)
        requires |T| == n + 2;
        requires seq_interp(T) < 2 * R(n) - 1;
        ensures T[n+1] == 0;
    {
        if T[n+1] != 0 {
            calc >= {
                seq_interp(T);
                interp(T, n + 2);
                word_interp(T, n + 1) + interp(T, n + 1);
                T[n+1] as int * postional_weight(n+1) + interp(T, n + 1);
                {
                    assert T[n+1] as int >= 1;
                }
                postional_weight(n+1) + interp(T, n + 1);
                power(BASE, n + 1) + interp(T, n + 1);
                power(BASE, n + 1);
                2 * R(n);
            }
            assert false;
        }
    }
}