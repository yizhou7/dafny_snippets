module MONTGOMERY {
    predicate congruent_def(a: int, b: int, n: int)
    {
        exists k : int :: a - b == n * k
    }

    lemma congruent_add_lema(a: int, b: int, c: int, d: int, n: int)
        requires n != 0;
        requires congruent_def(a, b, n) && congruent_def(c, d, n)
        ensures congruent_def(a + c, b + d, n)
    {
        var k_1, k_2 : int :| a - b == n * k_1 && c - d == n * k_2;
        
        calc == {
            (a + c) - (b + d);
            ==
            (a - b) + (c - d);
            ==
            n * k_1 + n * k_2;
            ==
            (k_1 + k_2) * n;
        }

        ghost var k := (k_1 + k_2);
        assert (a + c) - (b + d) == n * k;
    }

    lemma congruent_sub_lema(a: int, b: int, c: int, d: int, n: int)
        requires n != 0;
        requires congruent_def(a, b, n) && congruent_def(c, d, n)
        ensures congruent_def(a - c, b - d, n)
    {
        var k_1, k_2 : int :| a - b == n * k_1 && c - d == n * k_2;
        
        calc == {
            (a - c) - (b - d);
            ==
            n * k_1 - n * k_2;
            ==
            (k_1 - k_2) * n;
        }

        ghost var k := (k_1 +- k_2);
        assert (a - c) - (b - d) == n * k;
    }

    predicate divides_def(d:nat, n:int)
        requires d != 0;
    {
        (n % d) == 0
    }

    predicate gcd_def(a:nat, b:nat, gcd:nat)
    {
        gcd != 0
        && divides_def(gcd,a)
        && divides_def(gcd,b)
        && forall x:int :: gcd < x ==> !(divides_def(x,a) && divides_def(x,b))
    }

    predicate mod_inverse_def(a:nat, x:nat, n:nat)
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

    predicate montgomery_reduction_def(N: nat, R: nat, T: nat, m: nat)
        requires gcd_def(N, R, 1);
        requires 0 <= T < N * R;
    {
        var R_inv := mod_inverse(R, N);
        m == (T * R_inv) % N
    }

    lemma {:induction a} mulitiple_congruent_zero_lema(a: nat, b: nat)
        requires b != 0;
        ensures congruent_def(a * b, 0, b);
    {
        if a == 0 {
            ghost var k := a;
            assert a * b - 0 == b * k;
        } else {
            assert congruent_def((a - 1) * b, 0, b);
            ghost var k :| (a - 1) * b == b * k;
            calc == {
                (a * b);
                ==
                (a - 1) * b + b;
                ==
                b * (k + 1);
            }
            ghost var k' := (k + 1);
            assert a * b - 0 == b * k';
        }
    }

    lemma mulitiple_mod_zero_lema(a: int, b: nat)
        requires b != 0;
        ensures (a * b) % b == 0;
    {
        assume false;
    }

    lemma congruence_mod_connection_sufficient_lema(a: int, b: int, n: int)
        requires n != 0;
        requires a % n == b % n;
        ensures congruent_def(a, b, n);
    {
        var r1 := a % n;
        var k1 := a / n;
        assert a == r1 + k1 * n;

        var r2 := b % n;
        var k2 := b / n;
        assert b == r2 + k2 * n;

        assert r1 == r2;
        calc == {
            a - b;
            == 
            (r1 + k1 * n) - (r2 + k2 * n);
            == 
            k1 * n - k2 * n;
            == 
            (k1 - k2) * n;
        }
        var k := k1 - k2;
        assert a - b == n * k;
    }

    lemma congruence_mod_connection_necessary_lema(a: int, b: int, n: nat)
        requires n != 0;
        requires congruent_def(a, b, n);
        ensures a % n == b % n;
    {
        var r1 := a % n;
        var k1 := a / n;

        assert a == r1 + k1 * n;
        assert r1 == a - k1 * n;
        assert 0 <= r1 < n;
    
        // assert congruent_def(a, r1, n) by {
        //     assert a - r1 == n * k1;
        // }
        // var k1' :| a - r1 == n * k1';
        // assert k1' == k1;

        var r2 := b % n;
        var k2 := b / n;

        assert b == r2 + k2 * n;
        assert r2 == b - k2 * n;
        assert 0 <= r2 < n;
    
        // assert congruent_def(b, r2, n) by {
        //     assert b - r2 == n * k2;
        // }
        // var k2' :| b - r2 == n * k2';
        // assert k2' == k2;

        var k :| a - b == n * k;

        calc == {
            (r1 - r2) % n;
            ==
            {
                calc == {
                    r1 - r2;
                    ==
                    (a - k1 * n) - (b - k2 * n);
                    ==
                    (a - b) + (k2 - k1) * n;
                    ==
                    n * k + (k2 - k1) * n;
                    ==
                    (k + k2 - k1) * n;
                }
            }
            ((k + k2 - k1) * n) % n;
            ==
            {
                mulitiple_mod_zero_lema(k + k2 - k1, n);
            }
            0;
        }
        assert r1 == r2;
        assert a % n == b % n;

    }

    method montgomery_reduction(N: nat, R: nat, T: nat) returns (x: nat)
        requires R != 0;
        requires gcd_def(N, R, 1);
        requires 0 <= T < (N * R);
        // ensures montgomery_reduction_def(N, R, T, x);
    {
        var N_inv := mod_inverse(N, R);
        var m := T * (R - N_inv);
        calc == {
            (T + m * N) % R;
            ==
            (T + T * (R - N_inv) * N) % R;
            ==
            {
                assert T * (1 + (R - N_inv) * N) == T + T * (R - N_inv) * N;
            }
            (T * (1 + (R - N_inv) * N )) % R;
            ==
            {
                calc == {
                    (1 + (R - N_inv) * N ) % R;
                    ==
                    {
                        assert (R - N_inv) * N == R * N - N_inv * N;
                    }
                    (1 + R * N - N_inv * N) % R;
                    ==
                    {
                        var a := 1 + R * N - N_inv * N;
                        var b := 1 - N_inv * N;
                        assert a - b == R * N;
                        assert congruent_def(a, b, R);
                        congruence_mod_connection_necessary_lema(a, b, R);
                    }
                    (1 - N_inv * N) % R;
                }
            }
            // (T * (1 + (R  * N - N_inv * N))) % R; 
        }

        assume (T + m * N) % R == 0;
        var t := (T + m * N) / R;
        assert t * R - T == m * N;
        // assert congruent_def(t * R, T, N);
        x := if N <= t then (t - N)
        else t;
    }

    // method montgomery_mod(a: nat, b: nat, N:nat, R: nat) returns (x: nat)
    //     requires 0 < N < R &&  gcd_def(N, R, 1);
    // {
    //     var a' := (a * R) % N;
    //     var b' := (b * R) % N;
    //     var c' := montgomery_reduction(N, R, a' * b');
    //     x := montgomery_reduction(N, R, c');
    // }
}