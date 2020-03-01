include "Powers.dfy"
include "Congruence.dfy"

module NaiveMont {
    import opened Powers
    import opened Congruence

    predicate divs(d:nat, n:int)
        requires d != 0;
    {
        (n % d) == 0
    }

    predicate gcd_def(a:nat, b:nat, gcd:nat)
    {
        gcd != 0
        && divs(gcd,a)
        && divs(gcd,b)
        && forall x:int :: gcd < x ==> !(divs(x,a) && divs(x,b))
    }

    predicate mod_inverse_def(a:int, x:int, n:int)
        requires n != 0;
    {
        (x * a) % n == 1
    }

    function method mod_inverse(a:nat, n:nat) : (x: nat)
        requires n > 0;
        ensures mod_inverse_def(a, x, n);
        ensures x < n;
    {
        assume false;
        42
    }

    lemma mont_divisibility(T: int, M: nat, N: nat, N':nat, R: nat)
        requires 0 < N < R && gcd_def(N, R, 1);
        requires M == T * N' % R;
        requires cong(N' * N, -1, R);
        ensures (M * N + T) % R == 0;
    {
        assert cong(T * N' % R, T * N', R) by {
            mod_mod_lemma(T * N', R);
        }

        assert cong(T * N' * N , -T, R) by {
            calc ==> {
                cong(N' * N, -1, R);
                {
                    cong_mul_lemma(N' * N, -1, T, R);
                }
                cong((N' * N) * T, -T, R);
            }
        }
 
        assert cong(M * N, T * N' * N, R) by {
            assert cong(T * N' % R, T * N', R) by {
                mod_mod_lemma(T * N', R);
            }
            calc ==> {
                cong(T * N' % R, T * N', R);
                {
                    cong_mul_lemma(T * N' % R, T * N', N, R);
                }
                cong(T * N' % R * N, T * N' * N, R);
                {
                    assert M == T * N' % R;
                }
                cong(M * N, T * N' * N, R);
            }
        }

        assert (M * N + T) % R == 0 by {
            calc ==> {
                cong(M * N, T * N' * N, R) && cong(T * N' * N, -T, R);
                {
                    cong_trans_lemma(M * N, T * N' * N, -T, R);
                }
                cong(M * N, -T, R);
                {
                    cong_add_lemma(M * N, -T, T, R);
                }
                cong(M * N + T, 0, R);
                {
                    reveal cong();
                }
                (M * N + T) % R == 0 % R;
                {
                    assume 0 % R == 0;
                }
            }
        }
    }

    method mont_mul(A: nat, B: nat, N: nat, N_inv: nat, N':nat, R: nat, R_inv: nat) returns (P: nat)
        requires 0 < N < R && gcd_def(N, R, 1);
        // requires R_inv == mod_inverse(R, N);
        requires N_inv == mod_inverse(N, R);
        requires cong(N' * N, -1, R);
        // ensures P == A * B * R_inv % N;
    {
        var T := A * B;
        var M := T * N' % R;

        // assert cong(T * N' % R, T * N', R) by {
        //     mod_mod_lemma(T * N', R);
        // }

        // calc ==> {
        //     cong(T * N' % R, T * N', R);
        //     {
        //         cong_mul_lemma(T * N' % R, T * N', N, R);
        //     }
        //     cong(T * N' % R * N, T * N' * N, R);
        //     {
        //         calc ==> {
        //             cong(N' * N, -1, R);
        //             {
        //                 cong_mul_lemma(N' * N, -1, T, R);
        //             }
        //             cong(T * N' * N, -T, R);
        //             {
        //                 cong_trans(T * N' % R * N, T * N' * N, -T, R);
        //             }
        //             cong(T * N' % R * N, -T, R);
        //             {
        //                 assert M == T * N' % R;
        //             }
        //             cong(M * N, -T, R);
        //         }
        //     }
        //     cong(M * N, -T, R);
        //     {
        //         cong_add_lemma(M * N, -T, T, R);
        //     }
        //     cong(M * N + T, 0, R);
        //     (M * N + T) % R == 0 % R;
        // }

        assume false;
        // assert ((M * N) + T) % R == 0 % R by {
        //     assert cong((M * N) + T, 0, R);
        // }

        assume ((T + M * N) % R == 0);
        P := (T + M * N) / R;

        // assume false;
    }

}