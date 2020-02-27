include "NativeTypes.dfy"

module RSAE3 {
    import opened NativeTypes

    const E_32 :int := UINT32_MAX as int;

    // least significant -> most significant
    function method interpret(A: seq<uint32>) : int
        decreases A;
    {
        if |A| == 0 then 0
        else A[0] as int + E_32 * interpret(A[1..])
    }

    method seq_add(A: seq<uint32>, B: seq<uint32>, carry: uint32) returns (S : seq<uint32>)
        decreases A, B;
        requires |A| == |B|;
        ensures interpret(A) + interpret(B) + carry as int == interpret(S);
    {
        if |A| == 0 {
            return [carry];
        }
    
        var a: uint32, b: uint32 := A[0], B[0];
        var sum: uint64 := a as uint64 + b as uint64 + carry as uint64;
        var masked := and64(sum, UINT32_MAX as uint64) as uint32;

        var A', B' := A[1..], B[1..];

        if sum > UINT32_MAX as uint64 {
            var S' := seq_add(A', B', 1);
            S := [masked] + S';

            calc == {
                interpret(S);
                ==
                S[0] as int + E_32 * interpret(S[1..]);
                ==
                masked as int + E_32 * interpret(S[1..]);
                ==
                masked as int + E_32 * interpret(S');
                ==
                {
                    assert interpret(S') == interpret(A') + interpret(B') + 1;
                }
                masked as int + E_32 * (interpret(A') + interpret(B') + 1);
                ==
                masked as int + E_32 * interpret(A') + E_32 * interpret(B') + E_32;
                {
                    assume masked as int == sum as int - E_32;
                }
                sum as int + E_32 * interpret(A') + E_32 * interpret(B');
            }
            assert interpret(S) == sum as int + E_32 * interpret(A') + E_32 * interpret(B');
        } else {
            var S' := seq_add(A', B', 0);
            S := [masked] + S';

            calc == {
                interpret(S);
                ==
                S[0] as int + E_32 * interpret(S[1..]);
                ==
                masked as int + E_32 * interpret(S[1..]);
                ==
                masked as int + E_32 * interpret(S');
                ==
                {
                    assert interpret(S') == interpret(A') + interpret(B');
                }
                masked as int + E_32 * (interpret(A') + interpret(B'));
                ==
                masked as int + E_32 * interpret(A') + E_32 * interpret(B');
                ==
                sum as int + E_32 * interpret(A') + E_32 * interpret(B');
            }
            assert interpret(S) == sum as int + E_32 * interpret(A') + E_32 * interpret(B');
        }

        calc == {
            sum as int + E_32 * interpret(A') + E_32 * interpret(B');
            ==
            {
                assert sum as int == A[0] as int + B[0] as int + carry as int;
            }
            A[0] as int + B[0] as int + carry as int + E_32 * interpret(A') + E_32 * interpret(B');
            ==
            (A[0] as int + E_32 * interpret(A')) + (B[0] as int + E_32 * interpret(B')) + carry as int;
            ==
            {
                assert interpret(A) == A[0] as int + E_32 * interpret(A');
            }
            interpret(A) + (B[0] as int + E_32 * interpret(B')) + carry as int;
            ==
            {
                assert interpret(B) == B[0] as int + E_32 * interpret(B');
            }
            interpret(A) + interpret(B) + carry as int;
        }

        assert interpret(A) + interpret(B) + carry as int == interpret(S);
    }

    // method seq_sub(A: seq<uint32>, B: seq<uint32>) returns (x : seq<uint32>)
    //     decreases A, B;
    //     requires |A| == |B|
    // {
    //     if |A| == 0 {
    //         return [];
    //     }
        
    //     var a: uint32, b: uint32 := A[0], B[0];
    //     var diff: int64 := a as int64 - b as int64;

    //     if diff > 0 {
    //         var sub := seq_sub(A[1..], B[1..]);
    //         return [diff as uint32] + sub;
    //     }
        
    //     var diff_cast: uint64;
    //     var masked := and64(diff_cast, UINT32_MAX as uint64) as uint32;
    //     assume (masked as int + b as int == a as int + );
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