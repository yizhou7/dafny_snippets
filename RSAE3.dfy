include "NativeTypes.dfy"
include "Powers.dfy"
include "Congruences.dfy"

module RSAE3 {
    import opened NativeTypes
    import opened Powers
    import opened Congruences

    const E_2_32 :int := UINT32_MAX as int + 1;

    function method reinterpret_cast(a: int64) : uint64

    // |A[..i]| == i, interp A[..i] as an int 
    function interp(A: seq<uint32>, i: int) : int
        decreases i;
        requires 0 <= i <= |A|;
    {
        if i == 0 then 0
        else word_interp(A, i - 1) + interp(A, i - 1)
    }

    function word_interp(A: seq<uint32>, i: nat) : int
        requires i < |A|;
    {
        A[i] as int * postional_weight(i)
    }

    function seq_interp(A: seq<uint32>) : int
    {
        interp(A, |A|)
    }

    function postional_weight(i: nat) : int
    {
        power(E_2_32, i) as int
    }

    lemma postional_shift_lemma(i: int)
        requires i > 0;
        ensures postional_weight(i - 1) * E_2_32 == postional_weight(i);
    {
        calc == {
            postional_weight(i - 1) * E_2_32;
            ==
            power(E_2_32, i - 1) * E_2_32;
            {
                power_add_one_lema(E_2_32, i - 1);
            }
            power(E_2_32, i);
            ==
            postional_weight(i);
        }
    }

    lemma interp_expand(A: seq<uint32>, i: nat)
        requires 0  < i <= |A|;
        ensures interp(A, i) == A[i - 1] as int * postional_weight(i - 1) + interp(A, i - 1);
    {

    }

    lemma {:induction i} prefix_sum_lemma(S: seq<uint32>, S': seq<uint32>, i: nat)
        requires 0 <= i <= |S| && 0 <= i <= |S'|;
        requires S[..i] == S'[..i];
        ensures interp(S, i) == interp(S', i);
    {
        assert true;
    }

    method seq_add(A: seq<uint32>, B: seq<uint32>) returns (c: uint32, S:seq<uint32>)
        requires |A| == |B|;
        ensures seq_interp(A) + seq_interp(B) == seq_interp(S) + c as int * postional_weight(|A|);
    {
        var temp := new uint32[|A|];
        c, S := 0, temp[..];

        var i: nat := 0;

        while i < |A|
            invariant |S| == |A|;
            invariant 0 <= i <= |A|;
            decreases |A| - i;
            invariant interp(A, i) + interp(B, i) == interp(S, i) + c as int * postional_weight(i);
        {
            ghost var c_old, i_old: int := c, i;
            assert interp(A, i_old) + interp(B, i_old) == interp(S, i_old) + c_old as int * postional_weight(i_old);

            var sum: uint64 := A[i] as uint64 + B[i] as uint64 + c as uint64;
            var masked := and64(sum, UINT32_MAX as uint64) as uint32;
            assume masked as int + E_2_32 == sum as int;

            ghost var S_old := S;
            ghost var prefix_sum := interp(S_old, i);
            S := S[i := masked];

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
                    postional_weight(i - 1) * masked as int + postional_weight(i - 1) * E_2_32 + interp(S, i_old);
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

    method seq_sub(A: seq<uint32>, B: seq<uint32>) returns (b: uint32, S:seq<uint32>)
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

            assume diff < 0 ==> masked as int == diff as int + E_2_32 as int;
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
                    postional_weight(i - 1) * masked as int - postional_weight(i - 1) * E_2_32 + interp(S, i_old);
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

    method mont_red(T: seq<uint32>, n: nat, m: int, m': uint32, R: nat)
        returns (A': seq<uint32>)

        requires |T| == 2 * n as int;
        requires R == power(E_2_32, n as nat);
    {
        var A := T;

        var i := 0;
        while i < n
            invariant 0 <= i <= n;
            invariant |A| == 2 * n as int;
            decreases |A| - i;
            invariant forall j :: 0 <= j < i ==> A[j] == 0;
        {
            A := mont_red_step(A, n, i, m, m', R);
            i := i + 1;
        }
    }

    method mont_red_step(A: seq<uint32>, n: nat, i: nat, m: int, m': uint32, R: nat)
        returns (A': seq<uint32>)
        requires |A| == 2 * n as int;
        requires 0 <= i < n;
        requires forall j :: 0 <= j < i ==> A[j] == 0;

        ensures |A| == |A'|;
        ensures forall j :: 0 <= j <= i ==> A'[j] == 0;
    {
        var p_i := A[i] as nat * m' as nat; // there should be a better way
        var u_i :uint32 := (p_i % E_2_32) as uint32;

        A' := seq_add_pos(A, n, i, u_i, m, m');
    }

    method seq_add_pos(A: seq<uint32>, n: nat, i: nat, u_i: uint32, m: int, m': uint32) 
        returns (A': seq<uint32>)
        requires |A| == 2 * n as int;
        requires 0 <= i < n;
        requires forall j :: 0 <= j < i ==> A[j] == 0;

        ensures |A| == |A'|;
        ensures seq_interp(A) == seq_interp(A') + (u_i as int) * m * power(E_2_32, i);
        ensures forall j :: 0 <= j <= i ==> A'[j] == 0;
    {
        assume false;
    }

    // method modpow3(A: nat, N:nat, R: nat, RR: nat)
    //     requires RR == R * R;
    // {
    //     montMul(key, aR, a, RR);       /* aR = M * RR / R mod N   */
    //     montMul(key, aaR, aR, aR);     /* aaR = aR * MR / R mod N */
    //     montMul(key, aaa, aaR, a);     /* aaa = aaR * a / R mod N */
        
    //     if (geM(key, aaa)) {
    //        subM(key, aaa);
    //     }
    // }
}