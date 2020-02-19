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

    lemma residue_congruent_lema(a: int, b: int, n: int) 
        requires n != 0;
        requires a == b % n;
        ensures congruent_def(a, b, n);
    {
        var k := b / n;
        calc ==>
        {
            a + k * n == b;
            a + k * n - b == 0;
            a - b == - k * n;
            a - b == n * (-k);
        }
    }

    lemma residue_smaller_lema(a: nat, n:nat)
        requires n != 0;
        requires a < n;
        ensures a % n == a;
    {

    }

    lemma mul_distrubtive_lema(n: int, a: int, b: int, c: int)
        ensures n * (a + b + c) == n * a + n * b  + n * c;
    {
        assert true;
    }

    lemma congruent_mul_lema(a_1: int, b_1: int, a_2: int, b_2: int, n: int)
        requires congruent_def(a_1, b_1, n) && congruent_def(a_2, b_2, n);
        ensures congruent_def(a_1 * a_2, b_1 * b_2, n);
    {
        ghost var k_1, k_2 : int :| a_1 - b_1 == n * k_1 && a_2 - b_2 == n * k_2;

        calc == {
            a_1 * a_2 - b_1 * b_2;
            ==
            (n * k_1 + b_1) * (n * k_2 + b_2) - b_1 * b_2;
            ==
            n * n * k_1 * k_2 + n * b_1 * k_2 + n * k_1 * b_2;
            ==
            {
                assert n * b_1 * k_2 == n * (b_1 * k_2);
                assert n * k_1 * b_2 == n * (k_1 * b_2);
                assert n * n * k_1 * k_2 == n * (n * k_1 * k_2); // order of these assert somehow matter
            }
            n * (n * k_1 * k_2) + n * (b_1 * k_2) + n * (k_1 * b_2);
            ==
            {
                mul_distrubtive_lema(n, n * k_1 * k_2, b_1 * k_2, k_1 * b_2);
            }
            n * (n * k_1 * k_2 + b_1 * k_2 + k_1 * b_2);
        }
        ghost var k := n * k_1 * k_2 + b_1 * k_2 + k_1 * b_2;
        assert a_1 * a_2 - b_1 * b_2 == n * k;
        assert congruent_def(a_1 * a_2, b_1 * b_2, n);
    }

    lemma congruent_mul_const_lema(a: int, b: int, c: int, n: int)
        requires n != 0;
        requires congruent_def(a, b, n);
        ensures congruent_def(a * c, b * c, n);
    {
        assert congruent_def(c, c, n) by {
            congruent_identity_lema(c, n);
        }
        congruent_mul_lema(a, b, c, c, n);
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

    predicate montgomery_reduction_def(N: nat, R: nat, T: nat, m: nat)
        requires 0 <= T < N * R;
    {
        (m == (T * mod_inverse(R, N)) % N) && (m < N)
    }

    lemma montgomery_reduction_properties_lemma(N: nat, R: nat, T: nat, m: nat)
        requires 0 <= T < N * R;
        requires montgomery_reduction_def(N, R, T, m);
        ensures congruent_def(m, T * mod_inverse(R, N), N);
    {
        ghost var temp := T * mod_inverse(R, N);

        calc ==> {
            m == temp % N;
            m % N == temp % N;
            {
                congruent_mod_connection_sufficient_lema(m, temp, N);
            }
            congruent_def(m, temp, N);
            {
                assert temp == T * mod_inverse(R, N);
            }
            congruent_def(m, T * mod_inverse(R, N), N);
        }
    }

    // flaky
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

    lemma congruent_identity_lema(a:int, n:int)
        requires n != 0;
        ensures congruent_def(a, a, n);
    {
        var k := 0;
        assert a - a == n * k;
    }

    lemma mulitiple_mod_zero_lema(a: int, b: int)
        requires b != 0;
        ensures (a * b) % b == 0;
    {
        assume false;
    }

    lemma reaminder_mod_lema(a: nat, b: nat)
        requires b != 0;
        requires a < b;
        ensures a % b == a;
    {
    }

    lemma congruent_mod_connection_sufficient_lema(a: int, b: int, n: int)
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

    lemma congruent_mod_connection_necessary_lema(a: int, b: int, n: nat)
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

    lemma congruent_mul_inv_lema(a: int, b: int, b_inv: int, n: int)
        requires n != 0;
        requires mod_inverse_def(b, b_inv, n);
        ensures congruent_def(a, a * b * b_inv, n);
    {
        assert congruent_def(a, a * b * b_inv, n) by {
            assert congruent_def(1, b * b_inv, n) by {
                calc ==> {
                    1 % n == 1;
                    {
                        assert mod_inverse_def(b, b_inv, n);
                        assert (b * b_inv) % n == 1;
                    }
                    1 % n == (b * b_inv) % n;
                    {
                        congruent_mod_connection_sufficient_lema(1, b * b_inv, n);
                    }
                    congruent_def(1, b * b_inv, n);
                }
            }
            assert congruent_def(a, a, n) by {
                congruent_identity_lema(a, n);
            }
            congruent_mul_lema(1, b * b_inv, a, a, n);
        }
    }

    lemma congruent_transitivity_lema(a: int, b: int, c: int, n: nat)
        requires n != 0;
        requires congruent_def(a, b, n) && congruent_def(b, c, n);
        ensures congruent_def(a, c, n);
    {
        assert a % n == b % n by {
            congruent_mod_connection_necessary_lema(a, b, n);
        }
        assert b % n == c % n by {
            congruent_mod_connection_necessary_lema(b, c, n);
        }
        assert congruent_def(a, c, n) by {
            assert a % n == c % n;
            congruent_mod_connection_sufficient_lema(a, c, n);
        }
    }

    lemma congruent_reflexivity_lema(a: int, b: int, n: nat)
        requires n != 0;
        requires congruent_def(a, b, n);
        ensures congruent_def(b, a, n);
    {
        assert a % n == b % n by {
            congruent_mod_connection_necessary_lema(a, b, n);
        }
        assert congruent_def(b, a, n) by {
            assert b % n == a % n;
            congruent_mod_connection_sufficient_lema(b, a, n);
        }
    }

    lemma mod_inv_identity_lema(R: int, R_inv: int, N: nat)
        requires 0 < N < R;
        requires R_inv == mod_inverse(R, N);
        ensures congruent_def(R * R_inv, 1, N);
    {
        calc ==> {
            (R * R_inv) % N == 1;
            (R * R_inv) % N == 1 % N;
            {
                congruent_mod_connection_sufficient_lema(R * R_inv, 1, N);
            }
            congruent_def(R * R_inv, 1, N);
        }
    }

    lemma montgomery_reduction_sufficient_lema(N: nat, R: nat, T: nat, t: nat)
        requires gcd_def(N, R, 1);
        requires 0 <= T < N * R;
        requires (t * R) % N == T % N;
        requires t < N;
        ensures montgomery_reduction_def(N, R, T, t);
    {
        var R_inv := mod_inverse(R, N);
        var m := (T * R_inv) % N;

        assert congruent_def(t * R, T, N) by {
            assert (t * R) % N == T % N;
            congruent_mod_connection_sufficient_lema(t * R, T, N);
        }

        assert congruent_def(R_inv, R_inv, N) by {
            congruent_identity_lema(R_inv, N); 
        }

        calc ==> {
            congruent_def(t * R, T, N) && congruent_def(R_inv, R_inv, N);
            {
                congruent_mul_lema(t * R, T, R_inv, R_inv, N);
            }
            congruent_def(t * R * R_inv, T * R_inv, N);
            {
                assert congruent_def(t, t * R * R_inv, N) by {
                    congruent_mul_inv_lema(t, R, R_inv, N);
                }
                assert congruent_def(t, T * R_inv, N) by {
                    congruent_transitivity_lema(t, t * R * R_inv, T * R_inv, N);
                }
            }
            congruent_def(t, T * R_inv, N);
        }
        
        assert congruent_def(t, T * R_inv, N);
        assert t % N == (T * R_inv) % N by {
            congruent_mod_connection_necessary_lema(t, T * R_inv, N);
        }

        calc == {
            t % N - (T * R_inv) % N;
            ==
            {
                reaminder_mod_lema(t, N);
                assert t % N == t;
            }
            t - (T * R_inv) % N;
        }

        assert montgomery_reduction_def(N, R, T, t);
    }

    lemma reduction_bounded_lemma(N: nat, R: nat, T: int, m: nat, t: int)
        requires N != 0 && R != 0;
        requires 0 <= m < R;
        requires 0 <= T < (N * R);
        requires t == (T + m * N) / R;
        ensures 0 <= t < 2 * N;
    {
        calc ==> {
            0 <= m < R;
            {
                assert N > 0;
            }
            0 <= m * N < R * N;
            {
                assert 0 <= T < (N * R);
            }
            0 <= T + m * N < T + R * N;
            {
                assert 0 <= T < (N * R);
            }
            0 <= T + m * N < N * R + R * N;
            {
                assert N * R + R * N == 2 * N * R; 
            }
            0 <= T + m * N < 2 * N * R;
            {
                assert R > 0;
            }
            0 <= (T + m * N) / R < 2 * N;
            {
                assert t == (T + m * N) / R;
            }
            0 <= t < 2 * N;
        }     
    }

    lemma reduction_divisibie_lemma(N: nat, N': int, R: nat, T: int, m: int)
        requires N != 0 && R != 0;
        requires gcd_def(N, R, 1);
        requires 0 <= T < (N * R);
        requires m == (T * N') % R;
        requires congruent_def(N' * N, -1, R);
        ensures (T + m * N) % R == 0; 
    {
        assert congruent_def(m, T * N', R) by {
            assert m % R == (T * N') % R;
            congruent_mod_connection_sufficient_lema(m, T * N', R);
        }

        assert congruent_def(N, N, R) by {
            congruent_identity_lema(N, R);
        }

        calc ==> {
            congruent_def(m, T * N', R) && congruent_def(N, N, R);
            {
                congruent_mul_lema(m, T * N', N, N, R);
                assert congruent_def(m * N, N * T * N', R);
            }
            congruent_def(m * N, N * T * N', R);
            {
                assert N * T * N' == N' * N * T;
            }
            congruent_def(m * N, N' * N * T, R);
        }

        calc ==> {
            congruent_def(N' * N, -1, R);
            {
                assert congruent_def(T, T, R);
                congruent_mul_lema(N' * N, -1, T, T, R);
            }
            congruent_def(N' * N * T, -1 * T, R);
            {
                assert -1 * T == -T;
            }
            congruent_def(N' * N * T, -T, R);
        }

        calc ==> {
            congruent_def(m * N, N' * T * N, R) && congruent_def(N' * N * T, -T, R);
            {
                congruent_transitivity_lema(m * N, N' * N * T, -T, R);
            }
            congruent_def(m * N, -T, R);
            {
                assert congruent_def(T, T, R);
                congruent_add_lema(m * N, -T, T, T, R);
            }
            congruent_def(m * N + T, -T + T, R);
            {
                assert -T + T == 0;
                assert m * N + T == T + m * N;
            }
            congruent_def(T + m * N, 0, R);
            {
                congruent_mod_connection_necessary_lema(T + m * N, 0, R);
            }
            (T + m * N) % R == 0 % R; 
            (T + m * N) % R == 0; 
        }
        assert (T + m * N) % R == 0; 
    }

    lemma reduction_congruent_lemma(N: nat, R: nat, T: int, t: int, t': int)
        requires N != 0 && R != 0;
        requires congruent_def(t * R, T, N);
        requires t' == t - N;
        ensures congruent_def(t' * R, T, N);
    {
        assert congruent_def(N * R, 0, N) by {
            mulitiple_congruent_zero_lema(N, R);
        }

        ghost var a, d := t * R, 0;

        assert congruent_def(a, T, N);
        assert congruent_def(N * R, d, N);

        calc ==> {
            congruent_def(a, T, N) && congruent_def(N * R, d, N);
            {
                congruent_sub_lema(a, T, N * R, d, N);
            }
            congruent_def(a - N * R, T - d, N);
            {
                assert N - d == N;
            }
            congruent_def(a - N * R, T, N);
            {
                assert a == t * R;
            }
            congruent_def(t * R - N * R, T, N);
            {
                assert t * R - N * R == (t - N) * R;
            }
            congruent_def((t - N) * R, T, N);
            {
                assert t' == t - N;
            }
            congruent_def(t' * R, T, N);
        }
        assert congruent_def(t' * R, T, N);
    }

    method montgomery_reduction(N: nat, R: nat, T: int) returns (t: nat)
        requires 0 < N < R && gcd_def(N, R, 1);
        requires 0 <= T < (N * R);
        ensures montgomery_reduction_def(N, R, T, t);
    {
        var N_inv := mod_inverse(N, R);
        var N' := R - N_inv;

        assert congruent_def(N * R - N_inv * N, -1, R) by {
            assert congruent_def(N_inv * N, 1, R) by {
                calc ==> {
                    (N_inv * N) % R == 1;
                    (N_inv * N) % R == 1 % R;
                    {
                        congruent_mod_connection_sufficient_lema(N_inv * N, 1, R);
                    }
                    congruent_def(N_inv * N, 1, R);
                }
            }
            assert congruent_def(N * R, 0, R) by {
                mulitiple_congruent_zero_lema(N, R);
            }
            congruent_sub_lema(N * R, 0, N_inv * N, 1, R);
        }

        calc ==> {
            congruent_def(N * R - N_inv * N, -1, R);
            {
                assert N * R - N_inv * N == N * (R - N_inv);
            }
            congruent_def(N * (R - N_inv), -1, R);
            {
                assert N' == R - N_inv;
            }
            congruent_def(N * N', -1, R);
        }

        assert congruent_def(N' * N, -1, R);

        var m := (T * N') % R;        

        assert (T + m * N) % R == 0 by {
            reduction_divisibie_lemma(N, N', R, T, m);
        }

        t := (T + m * N) / R;

        assert 0 <= t < 2 * N by {
            reduction_bounded_lemma(N, R, T, m, t);
        }

        assert congruent_def(t * R, T, N) by {
            assert t * R - T == N * m;
        }

        if t >= N {
            var t' := t - N;
            assert 0 <= t' < N;
            assert congruent_def(t' * R, T, N) by {
                reduction_congruent_lemma(N, R, T, t, t');
            }
            t := t';
            assert 0 <= t < N;
            assert congruent_def(t * R, T, N);
        }
        assert 0 <= t < N;

        assert (t * R) % N == T % N by {
            assert congruent_def(t * R, T, N);
            congruent_mod_connection_necessary_lema(t * R, T, N);
        }

        assert montgomery_reduction_def(N, R, T, t) by {
            montgomery_reduction_sufficient_lema(N, R, T, t);
        }
    }

    lemma montgomery_representation_lemma(a: nat, a': nat, R: nat, R_inv: nat, N: nat)
        requires 0 < N < R && gcd_def(N, R, 1);
        requires R_inv == mod_inverse(R, N);
        requires congruent_def(a', a * R, N);
        ensures congruent_def(a' * R_inv, a, N);
    {
        calc ==> {
            congruent_def(a', a * R, N);
            {
                congruent_mul_const_lema(a', a * R, R_inv, N);
            }
            congruent_def(a' * R_inv, a * R * R_inv, N);
            {
                assert congruent_def(R * R_inv, 1, N) by {
                    mod_inv_identity_lema(R, R_inv, N);
                }
                calc ==>
                {
                    congruent_def(R * R_inv, 1, N);
                    {
                        congruent_mul_const_lema(R * R_inv, 1, a, N);
                    }
                    congruent_def(R * R_inv * a, a, N);
                    {
                       assert a * R * R_inv == R * R_inv * a;
                    }
                    congruent_def(a * R * R_inv, a, N);
                }
                assert congruent_def(a' * R_inv, a, N) by {
                    congruent_transitivity_lema(a' * R_inv, a * R * R_inv, a, N);
                }
            }
            congruent_def(a' * R_inv, a, N);
        }
    }

    lemma montgomery_mul_mod_lema(a: nat, b: nat, c: nat, a': nat, b': nat,  c': nat, R: nat, R_inv: nat, N: nat)
        requires 0 < N < R && gcd_def(N, R, 1);
        requires R_inv == mod_inverse(R, N);
        requires congruent_def(c', (a' * b') * R_inv, N);
        requires congruent_def(c, c' * R_inv, N);
        requires congruent_def(a', a * R, N);
        requires congruent_def(b', b * R, N);
        ensures congruent_def(c, a * b, N);
    {
        calc ==> {
            congruent_def(c', (a' * b') * R_inv, N);
            {
                congruent_mul_const_lema(c', (a' * b') * R_inv, R_inv, N);
            }
            congruent_def(c' * R_inv, (a' * b') * R_inv * R_inv, N);
            {
                assert congruent_def(c, c' * R_inv, N);
                congruent_transitivity_lema(c, c' * R_inv, (a' * b') * R_inv * R_inv, N); 
            }
            congruent_def(c, (a' * b') * R_inv * R_inv, N);
            {
                assert a' * R_inv * b' * R_inv == (a' * b') * R_inv * R_inv;
            }
            congruent_def(c, a' * R_inv * b' * R_inv, N);
        }

        assert congruent_def(c, a * b, N) by {
            assert congruent_def(a' * R_inv * b' * R_inv, a * b, N) by {
                assert congruent_def(a' * R_inv, a, N) by {
                    montgomery_representation_lemma(a, a', R, R_inv, N);
                }
                assert congruent_def(b' * R_inv, b, N) by {
                    montgomery_representation_lemma(b, b', R, R_inv, N);
                }
                congruent_mul_lema(a' * R_inv, a, b' * R_inv, b, N);
            }
            assert congruent_def(c, a' * R_inv * b' * R_inv, N);
            congruent_transitivity_lema(c, a' * R_inv * b' * R_inv, a * b, N); 
        }
    }

    method montgomery_mul_mod(a: nat, b: nat, N:nat, R: nat) returns (c: nat)
        requires 0 < N < R && gcd_def(N, R, 1);
        ensures c == (a * b) % N;
    {
        var a' := (a * R) % N;
        var b' := (b * R) % N;
        assert a' < N && b' < N;
        assert a' * b' < N * N;

        ghost var R_inv := mod_inverse(R, N);

        var c' := montgomery_reduction(N, R, a' * b');
        c := montgomery_reduction(N, R, c');

        assert congruent_def(c, a * b, N) by {
            assert congruent_def(a', a * R, N) by {
                assert a' == (a * R) % N;
                residue_congruent_lema(a', a * R, N);
            }

            assert congruent_def(b', b * R, N) by {
                assert b' == (b * R) % N;
                residue_congruent_lema(b', b * R, N);
            }
            assert congruent_def(c', (a' * b') * R_inv, N) by {
                assert montgomery_reduction_def(N, R, a' * b', c');
                montgomery_reduction_properties_lemma(N, R, a' * b', c');
            }

            assert congruent_def(c, c' * R_inv, N) by {
                assert montgomery_reduction_def(N, R, c', c);
                montgomery_reduction_properties_lemma(N, R, c', c);
            }

            montgomery_mul_mod_lema(a, b, c, a', b', c', R, R_inv, N);
        }

        assert c % N == (a * b) % N by {
            congruent_mod_connection_necessary_lema(c, a * b, N);
        }

        assert c % N == c by {
            residue_smaller_lema(c, N);
        }

        assert c == (a * b) % N;
    }

    // lemma not_so_interesting_lemma(a: int, b: int, c: int, n: nat)
    //     requires n != 0;
    //     requires a == b % n;
    //     ensures (b * c) % n == (a * c) % n;
    // {
    //     ghost var d := (b * c) % n;
    //     assert congruent_def(a, b, n) by {
    //         residue_congruent_lema(a, b, n);
    //     }
    //     assert congruent_def(a * c, b * c, n) by {
    //         congruent_mul_const_lema(a, b, c, n);
    //     }
    //     assert a * c % n == b * c % n by {
    //         congruent_mod_connection_necessary_lema(a * c, b * c, n);
    //     }
    // }

    method montgomery_exp_mod(m: nat, b: nat, N:nat, R: nat) returns (c: nat)
        requires 0 < N < R && gcd_def(N, R, 1);
        // ensures c == (a * b) % N;
    {
        var m' : nat := (m * R) % N;
        var c' : nat := m';
    
        var i := 1;

        while i < b
            decreases b - i;
        {
            c' := montgomery_mul_mod(c', m', N, R);
            i := i + 1;
        }
    }


}