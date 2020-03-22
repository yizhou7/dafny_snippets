include "Powers.dfy"

module Congruences {
    import opened Powers

    predicate {:opaque} cong(a: int, b: int, n: int)
        requires n != 0;
    {
        a % n == b % n
    }

    lemma cong_equiv_lemma(a: int, b: int, n: int)
        requires n != 0;
        ensures cong(a, b, n) == ((a - b) % n == 0);
    {
        if cong(a, b, n) {
            reveal cong();

            ghost var k1 := a / n;
            ghost var k2 := b / n;
            assert k1 * n + a % n == a;
            assert k2 * n + b % n == b;
    
            calc == {
                (a - b) % n;
                (k1 * n + a % n - k2 * n - b % n) % n;
                (k1 * n - k2 * n) % n;
                ((k1 - k2) * n) % n;
                {
                    mod_mul_lemma(k1 - k2, n, n);
                }
                0;
            }
            assert cong(a, b, n) ==> (a - b) % n == 0;
        }

        assume cong(a, b, n) <== ((a - b) % n == 0);
    }

    lemma mod_mul_lemma(a: int, b: int, n: int)
        requires n != 0;
        requires b % n == 0;
        ensures a * b % n == 0;
    {
        assume false;
    }

    lemma mod_div_inv_leamma(a: int, b: int, b_inv: int, n: int)
        requires n != 0 && b != 0
        requires cong(b * b_inv, 1, n);
        requires a % b == 0;
        ensures cong(a * b_inv, a / b, n);
    {
        assert cong(a / b, a / b, n) by {
            reveal cong();
        }

        calc ==> {
            cong(a / b, a / b, n);
            {
                cong_mul_lemma_1(a / b, a / b, b * b_inv, n);
            }
            cong(a * b_inv,  (a / b) * b_inv * b, n);
            {
                assert cong((a / b) * b * b_inv, a / b, n) by {
                    assert cong(b * b_inv, 1, n);
                    cong_mul_lemma_1(b * b_inv, 1, a / b, n);
                }
                assert cong(a * b_inv, a / b, n) by {
                    cong_trans_lemma(a * b_inv,  (a / b) * b_inv * b, a / b, n);
                } 
            }
            cong(a * b_inv, a / b, n);
        }
    }

    lemma cong_trans_lemma(a: int, b: int, c: int, n: int)
        requires n != 0;
        requires cong(a, b, n) && cong(b, c, n);
        ensures cong(a, c, n);
    {
        reveal cong();
    }

    lemma cong_residual_lemma(a: int, b: nat, n: nat)
        requires n != 0;
        ensures (cong(a, b, n) && b < n) <==> (b == a % n);
    {
        reveal cong();        
    }

    lemma cong_mod_lemma(a: int, n: int)
        requires n != 0;
        ensures cong((a % n), a, n);
    {
        reveal cong();
    }

    lemma cong_mul_lemma_1(a: int, b: int, c: int, n: int)
        requires n != 0;
        requires cong(a, b, n);
        ensures cong(a * c, b * c, n);
    {
        ghost var k1 := a / n;
        ghost var k2 := b / n;
        assert k1 * n + a % n == a;
        assert k2 * n + b % n == b;

        calc == {
            (a * c - b * c) % n;
            ((k1 * n + a % n - k2 * n - b % n) * c) % n;
            {
                reveal cong();
                assert a % n == b % n;
            }
            ((k1 * n - k2 * n) * c) % n;
            ((k1 - k2 ) * c * n) % n;
            {
                assert c * n % n == 0 by {
                    mod_mul_lemma(c, n, n);
                }
            }
            // 0;
        }
        // assert (a * c) % n == (b * c) % n by {
        //     assert (a * c - b * c) % n == 0;
        //     cong_equiv(a * c, b * c, n);
        // }
        // assert (a * c) % n == (b * c) % n;
        assume false;
    }

    lemma cong_mul_lemma_2(a1: int, b1: int, a2: int, b2: int, n: int)
        requires n != 0;
        requires cong(a1, b1, n) && cong(a2, b2, n);
        // ensures cong(a1 * a_2, b1 * b_2, n);
    {
        reveal cong();
        assert a1 % n == b1 % n;

        // ghost var k1 := a1 / n;
        // ghost var k2 := b1 / n;

        // assert k1 * n + a1 % n == a1;
        // assert k2 * n + b1 % n == b1;

        // ghost var k_1 : int :| a1 - b1 == n * k_1;

        // assert a2 % n == b2 % n;
        //  && a_2 - b_2 == n * k_2;

        // calc == {
        //     a_1 * a_2 - b1 * b_2;
        //     ==
        //     (n * k_1 + b1) * (n * k_2 + b_2) - b1 * b_2;
        //     ==
        //     n * n * k_1 * k_2 + n * b1 * k_2 + n * k_1 * b_2;
        //     ==
        //     {
        //         assert n * b1 * k_2 == n * (b1 * k_2);
        //         assert n * k_1 * b_2 == n * (k_1 * b_2);
        //         assert n * n * k_1 * k_2 == n * (n * k_1 * k_2); // order of these assert somehow matter
        //     }
        //     n * (n * k_1 * k_2) + n * (b1 * k_2) + n * (k_1 * b_2);
        //     ==
        //     {
        //         // mul_distrubtive_lemma(n, n * k_1 * k_2, b1 * k_2, k_1 * b_2);
        //         assume false;
        //     }
        //     n * (n * k_1 * k_2 + b1 * k_2 + k_1 * b_2);
        // }
        // ghost var k := n * k_1 * k_2 + b1 * k_2 + k_1 * b_2;
        // assert a_1 * a_2 - b1 * b_2 == n * k;

        assume false;

        // assert cong_def(a_1 * a_2, b1 * b_2, n);
    }



    lemma cong_add_lemma_1(a: int, b: int, c: int, n: int)
        requires n != 0;
        requires cong(a, b, n);
        ensures cong(a + c, b + c, n);

    lemma cong_add_lemma_2(a: int, b: int, c: int, d: int, n: int)
        requires n != 0;
        requires cong(a, b, n) && cong(c, d, n);
        ensures cong(a + c, b + d, n);
    
    lemma cong_add_lemma_3(a: int, m: int, n: int)
        requires n != 0;
        requires m % n == 0;
        ensures cong(a, a + m, n);

    lemma cong_power_lemma(a: int, b: int, e: nat, n: int)
        requires n != 0;
        requires cong(a, b, n);
        ensures  cong(power(a, e), power(b, e), n);
}
