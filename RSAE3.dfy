include "NativeTypes.dfy"
include "Powers.dfy"

module RSAE3 {
    import opened NativeTypes
    import opened Powers

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
            var c_old, i_old: int := c, i;
            assert interp(A, i_old) + interp(B, i_old) == interp(S, i_old) + c_old as int * postional_weight(i_old);

            var sum: uint64 := A[i] as uint64 + B[i] as uint64 + c as uint64;
            var masked := and64(sum, UINT32_MAX as uint64) as uint32;

            ghost var S_old := S;
            ghost var prefix_sum := interp(S_old, i);
            S := S[i := masked];

            assert interp(S, i_old) == interp(S_old, i_old) by {
                prefix_sum_lemma(S, S_old, i_old);
            }

            assert prefix_sum == interp(S, i_old);

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
                assume masked as int + E_2_32 == sum as int;

                c := 1;
                calc == {
                    postional_weight(i - 1) * (sum as int) + interp(S, i_old);
                    postional_weight(i - 1) * masked as int + postional_weight(i - 1) * E_2_32 + interp(S, i_old);
                    {
                        postional_shift_lemma(i);
                    }
                    postional_weight(i - 1) * masked as int + postional_weight(i) + interp(S, i_old);
                }
                assert interp(A, i) + interp(B, i) == interp(S, i) + postional_weight(i);
            } else {
                c := 0;
                assert interp(A, i) + interp(B, i) == interp(S, i);
            }

            assert interp(A, i) + interp(B, i) == interp(S, i) + c as int * postional_weight(i);
        }

        assert seq_interp(A) + seq_interp(B) == seq_interp(S) + c as int * postional_weight(i);
    }

    /*
    function hd_rec_interp(A: seq<uint32>) : int
    {
        hd_rec_interp_aux(A, 0)
    }

    function hd_rec_interp_aux(A: seq<uint32>, i: nat) : int
        decreases |A| - i as int; 
        requires 0 <= i <= |A|;
    {
        if i == |A| then 0
        else word_interp(A, i) + hd_rec_interp_aux(A, i + 1)
    }

    function tl_rec_interp(A: seq<uint32>) : int
    {
        tl_rec_interp_aux(A, 0, 0)
    }

    function tl_rec_interp_aux(A: seq<uint32>, i: nat, acc: int) : int
        decreases |A| - i as int; 
        requires 0 <= i <= |A|;
    {
        if i == |A| then acc
        else tl_rec_interp_aux(A, i + 1, acc + word_interp(A, i))
    }

    lemma interp_sufficient(A: seq<uint32>)
        ensures tl_rec_interp(A) == hd_rec_interp(A);
    {
        assume tl_rec_interp(A) == hd_rec_interp(A);
    }
    */


    // method rec_seq_add(A: seq<uint32>, B: seq<uint32>, carry: uint32) returns (S : seq<uint32>)
    //     decreases A, B;
    //     requires |A| == |B|;
    //     ensures interpret(A) + interpret(B) + carry as int == interpret(S);
    // {
    //     if |A| == 0 {
    //         return [carry];
    //     }
    
    //     var a: uint32, b: uint32 := A[0], B[0];
    //     var sum: uint64 := a as uint64 + b as uint64 + carry as uint64;
    //     var masked := and64(sum, UINT32_MAX as uint64) as uint32;

    //     var A', B' := A[1..], B[1..];

    //     if sum > UINT32_MAX as uint64 {
    //         assume masked as int == sum as int - E_2_32;

    //         var S' := rec_seq_add(A', B', 1);
    //         S := [masked] + S';

    //         calc == {
    //             interpret(S);
    //             ==
    //             masked as int + E_2_32 * interpret(S');
    //             ==
    //             {
    //                 assert interpret(S') == interpret(A') + interpret(B') + 1;
    //             }
    //             masked as int + E_2_32 * (interpret(A') + interpret(B') + 1);
    //             ==
    //             masked as int + E_2_32 * interpret(A') + E_2_32 * interpret(B') + E_2_32;
    //             {
    //                 assert masked as int == sum as int - E_2_32;
    //             }
    //             sum as int + E_2_32 * interpret(A') + E_2_32 * interpret(B');
    //         }
    //         assert interpret(S) == sum as int + E_2_32 * interpret(A') + E_2_32 * interpret(B');
    //     } else {
    //         var S' := rec_seq_add(A', B', 0);
    //         S := [masked] + S';

    //         calc == {
    //             interpret(S);
    //             ==
    //             masked as int + E_2_32 * interpret(S');
    //             ==
    //             {
    //                 assert interpret(S') == interpret(A') + interpret(B');
    //             }
    //             masked as int + E_2_32 * (interpret(A') + interpret(B'));
    //             ==
    //             masked as int + E_2_32 * interpret(A') + E_2_32 * interpret(B');
    //             ==
    //             sum as int + E_2_32 * interpret(A') + E_2_32 * interpret(B');
    //         }
    //         assert interpret(S) == sum as int + E_2_32 * interpret(A') + E_2_32 * interpret(B');
    //     }

    //     calc == {
    //         sum as int + E_2_32 * interpret(A') + E_2_32 * interpret(B');
    //         ==
    //         {
    //             assert sum as int == A[0] as int + B[0] as int + carry as int;
    //         }
    //         A[0] as int + B[0] as int + carry as int + E_2_32 * interpret(A') + E_2_32 * interpret(B');
    //         ==
    //         (A[0] as int + E_2_32 * interpret(A')) + (B[0] as int + E_2_32 * interpret(B')) + carry as int;
    //         ==
    //         {
    //             assert interpret(A) == A[0] as int + E_2_32 * interpret(A');
    //         }
    //         interpret(A) + (B[0] as int + E_2_32 * interpret(B')) + carry as int;
    //         ==
    //         {
    //             assert interpret(B) == B[0] as int + E_2_32 * interpret(B');
    //         }
    //         interpret(A) + interpret(B) + carry as int;
    //     }

    //     assert interpret(A) + interpret(B) + carry as int == interpret(S);
    // }



    // lemma {:induction A, B} shift_preservation(A: seq<uint32>, B: seq<uint32>)
    //     decreases A, B;
    //     requires |A| == |B|;
    //     requires interpret(A) >= interpret(B);
    //     ensures |A| != 0 ==> interpret(A[1..]) >= interpret(B[1..])
    // {
    //     assert true;
    // }

    // lemma {:induction i} shifts_order_preservation(A: seq<uint32>, B: seq<uint32>, i: nat)
    //     requires |A| == |B|;
    //     requires interpret(A) >= interpret(B);
    //     requires 0 <= i < |A|;
    //     ensures interpret(A[i..]) >= interpret(B[i..])
    // {
    //     if i != 0 {
    //         var A', B' := A[i - 1..], B[i - 1..];
    //         assert interpret(A') >= interpret(B');
    //         shift_preservation(A', B');
    //     }
    // }

    // method rec_seq_sub(A: seq<uint32>, B: seq<uint32>, borrow: uint32) returns (S : seq<uint32>)
    //     decreases A, B;
    //     requires |A| == |B|;
    //     requires interpret(A) >= interpret(B);
    //     ensures interpret(A) - interpret(B) - borrow as int == interpret(S);
    // {
    //     if |A| == 0 {
    //         assume borrow == 0;
    //         return [0];
    //     }
    
    //     var a: uint32, b: uint32 := A[0], B[0];
    //     var diff: int64 := a as int64 - b as int64 - borrow as int64;
    //     var masked := and64(reinterpret_cast(diff), UINT32_MAX as uint64) as uint32;

    //     var A', B' := A[1..], B[1..];

    //     assert interpret(A') >= interpret(B') by {
    //         shift_preservation(A', B');
    //     }

    //     if diff < 0 {
    //         assume masked as int == diff as int + E_2_32 as int;

    //         var S' := rec_seq_sub(A', B', 1);
    //         S := [masked] + S';

    //         calc == {
    //             interpret(S);
    //             ==
    //             masked as int + E_2_32 * interpret(S');
    //             ==
    //             {
    //                 assert interpret(S') == interpret(A') - interpret(B') - 1;
    //             }
    //             masked as int + E_2_32 * (interpret(A') - interpret(B') - 1);
    //             ==
    //             masked as int + E_2_32 * interpret(A') - E_2_32 * interpret(B') - E_2_32;
    //             ==
    //             diff as int + E_2_32 * interpret(A') - E_2_32 * interpret(B');
    //         }
    //     } else {
    //         assume diff as int == masked as int;

    //         var S' := rec_seq_sub(A', B', 0);
    //         S := [masked] + S';

    //         calc == {
    //             interpret(S);
    //             ==
    //             masked as int + E_2_32 * interpret(S');
    //             ==
    //             {
    //                 assert interpret(S') == interpret(A') - interpret(B');
    //             }
    //             masked as int + E_2_32 * (interpret(A') - interpret(B'));
    //             ==
    //             diff as int + E_2_32 * interpret(A') - E_2_32 * interpret(B');
    //         }
    //     }

    //     calc == {
    //         diff as int + E_2_32 * interpret(A') - E_2_32 * interpret(B');
    //         ==
    //         {
    //             assert diff as int == A[0] as int - B[0] as int - borrow as int;
    //         }
    //         A[0] as int - B[0] as int - borrow as int + E_2_32 * interpret(A') - E_2_32 * interpret(B');
    //         ==
    //         (A[0] as int + E_2_32 * interpret(A')) - (B[0] as int + E_2_32 * interpret(B')) - borrow as int;
    //         ==
    //         {
    //             assert interpret(A) == A[0] as int + E_2_32 * interpret(A');
    //         }
    //         interpret(A) - (B[0] as int + E_2_32 * interpret(B')) - borrow as int;
    //         ==
    //         {
    //             assert interpret(B) == B[0] as int + E_2_32 * interpret(B');
    //         }
    //         interpret(A) - interpret(B) - borrow as int;
    //     }
    // }

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