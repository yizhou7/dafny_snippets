include "NativeTypes.dfy"
include "Powers.dfy"

module RSAE3 {
    import opened NativeTypes
    import opened Powers

    const E_2_32 :int := UINT32_MAX as int + 1;

    function method reinterpret_cast(a: int64) : uint64

    // least significant -> most significant
    function head_rec_interp(A: seq<uint32>) : int
        decreases A;
    {
        if |A| == 0 then 0
        else A[0] as int + E_2_32 * head_rec_interp(A[1..])
    }

    function tail_rec_interp(A: seq<uint32>) : int
    {
        tail_rec_interp_aux(A, 0, 0)
    }

    function word_interp(A: seq<uint32>, i: nat) : int
        requires i < |A|;
    {
        A[i] as int * power(E_2_32, i) as int
    }

    function tail_rec_interp_aux(A: seq<uint32>, i: nat, acc: int) : int
        decreases |A| - i as int; 
        requires 0 <= i <= |A|;
    {
        if i == |A| then acc
        else tail_rec_interp_aux(A, i + 1, word_interp(A, i))
    }

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

    // method seq_add(A: seq<uint32>, B: seq<uint32>) returns (S : seq<uint32>)
    //     requires |A| == |B|;
    //     // ensures interpret(A) + interpret(B) == interpret(S);
    // {
    //     var carry: uint32 := 0;
    //     var index := 0;
    //     // ghost var A', B' := A[..index], B[..index];
    //     var A_, B_ := A, B;
    //     S := [];

    //     // assert (|A[..0]| == 0);
    //     while index < |A|
    //         decreases |A| - index
    //     {
    //         var A', B' := A[..index], B[..index];

    //         assume interpret(A') + interpret(B') == interpret(S) + carry as int * power(E_2_32 as int, index);

    //         var a: uint32, b: uint32 := A[index], B[index];

    //         var sum: uint64 := a as uint64 + b as uint64 + carry as uint64;
    //         var masked := and64(sum, UINT32_MAX as uint64) as uint32;
            
    //         if sum > UINT32_MAX as uint64 {
    //             S := S + [masked];
    //             carry := 1;
    //         } else {
    //             S := S + [masked];
    //             carry := 0;
    //         }

    //         index := index + 1;
    //         A', B' := A[..index], B[..index];
    //         assume interpret(A') + interpret(B') == interpret(S) + carry as int * power(E_2_32 as int, index);
    //     }
    
    //     assume false;
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