include "NativeTypes.dfy"
include "Powers.dfy"
include "Congruences.dfy"
include "SeqInt.dfy"

module RSAE3 {
    import opened NativeTypes
    import opened Powers
    import opened Congruences
    import opened SeqInt

    lemma mont_mul_div_aux_lemma_2(y: int, x: int, m: int, a: int, m': int)
        requires cong(m' * m, -1, BASE);
        ensures cong(m * (((a + x * y) * m') % BASE), -(a + x * y), BASE);
    {
        assert A_1: cong(((a + x * y) * m') % BASE, (a + x * y) * m', BASE) by {
            mod_mod_lemma((a + x * y) * m', BASE);
        }

        ghost var temp_1 := m * (((a + x * y) * m') % BASE);
        ghost var temp_2 := -(a + x * y);
   
        calc ==> {
            cong(((a + x * y) * m') % BASE, (a + x * y) * m', BASE);
            {
                cong_mul_lemma(((a + x * y) * m') % BASE, (a + x * y) * m', m, BASE);
            }
            cong(temp_1, m * (a + x * y) * m', BASE);
            {
                assert m * (a + x * y) * m' == m * m' * (a + x * y);
            }
            cong(temp_1, m * m' * (a + x * y), BASE);
            {
                assert cong(m * m' * (a + x * y), -(a + x * y), BASE) by {
                    assert cong(m' * m, -1, BASE);
                    cong_mul_lemma(m' * m, -1, (a + x * y), BASE);
                }
                cong_trans_lemma(temp_1, m * m' * (a + x * y), -(a + x * y), BASE);
            }
            cong(temp_1, -(a + x * y), BASE);
            cong(temp_1, temp_2, BASE);
        }

        assert cong(temp_1, temp_2, BASE) by {
            reveal A_1;
        }

        calc ==> {
            cong(temp_1, temp_2, BASE);
            cong(m * (((a + x * y) * m') % BASE), temp_2, BASE);
            cong(m * (((a + x * y) * m') % BASE), -(a + x * y), BASE);
        }

        assert cong(m * (((a + x * y) * m') % BASE), -(a + x * y), BASE);
    }

    lemma mont_mul_div_aux_lemma_1(y: int, x: int, m: int, a: int, m': int)
        requires cong(m' * m, -1, BASE);
        ensures cong(y * x + m * (((a + x * y) * m') % BASE) + a, 0, BASE);
    {
        ghost var temp_1 := m * (((a + x * y) * m') % BASE);
        ghost var temp_2 := -(a + x * y);
        ghost var temp_3 := x * y;

        assert cong(temp_1, temp_2, BASE) by {
            mont_mul_div_aux_lemma_2(y, x, m, a, m');
        }

        calc ==> {
            cong(temp_1, temp_2, BASE);
            {
                cong_add_lemma_1(temp_1, temp_2, temp_3, BASE);
            }
            cong(temp_1 + temp_3, temp_2 + temp_3, BASE);
            cong(temp_1 + temp_3, -(a + x * y) + x * y, BASE);
            cong(temp_1 + temp_3, -a - x * y + x * y, BASE);
            cong(temp_1 + temp_3, -a, BASE);
            {
                cong_add_lemma_1(temp_1 + temp_3, -a, a, BASE);
            }
            cong(temp_1 + temp_3 + a, 0, BASE);
            cong(temp_3 + temp_1 + a, 0, BASE);
            cong(x * y + temp_1 + a, 0, BASE);
            cong(x * y + m * (((a + x * y) * m') % BASE) + a, 0, BASE);
        }
        assert cong(x * y + m * (((a + x * y) * m') % BASE) + a, 0, BASE);
    }

    lemma mont_mul_divisible_lemma(m: seq<uint32>,
        x: seq<uint32>,
        y: seq<uint32>,
        P_1: seq<uint32>,
        P_2: seq<uint32>,
        S: seq<uint32>,
        A: seq<uint32>,
        A': seq<uint32>,
        i: nat,
        u_i: uint32,
        m': uint32,
        n: nat)

        requires n > 2 && i < n;
        requires |m| == |x| == |y| == n;
        requires |P_1| ==|P_2| == n + 1;
        requires |S| == |A| == n + 2;
        requires |A'| == n + 3;
        requires cong(m' as int * seq_interp(m), -1, BASE);

        requires u_i as int == ((A[0] as int + x[i] as int * y[0] as int) * m' as int) % BASE;

        requires cong(P_1[0] as int, y[0] as int * x[i] as int, BASE);
        requires cong(P_2[0] as int, m[0] as int * u_i as int, BASE);
        requires cong(A'[0] as int, A[0] as int + S[0] as int, BASE);

        requires seq_interp(A) + seq_interp(S) == seq_interp(A');

        requires cong(S[0] as int, P_1[0] as int + P_2[0] as int, BASE);
        ensures cong(A'[0] as int, 0, BASE);
    {
        assert cong(m' as int * m[0] as int, -1, BASE) by {
                lsw_inverse_lemma(m, m');
        }

        calc ==> {
            cong(S[0] as int, P_1[0] as int + P_2[0] as int, BASE);
            {
                cong_add_lemma_1(S[0] as int, P_1[0] as int + P_2[0] as int, A[0] as int,BASE);
            }
            cong(S[0] as int + A[0] as int, P_1[0] as int + P_2[0] as int + A[0] as int, BASE);
            {
                cong_trans_lemma(A'[0] as int, A[0] as int + S[0] as int,
                    P_1[0] as int + P_2[0] as int + A[0] as int,
                    BASE);
            }
            cong(A'[0] as int, P_1[0] as int + P_2[0] as int + A[0] as int, BASE);
            {
                assert cong(P_1[0] as int + P_2[0] as int + A[0] as int, y[0] as int * x[i] as int + m[0] as int * u_i as int + A[0] as int, BASE) by {
                    assert cong(P_1[0] as int + P_2[0] as int, y[0] as int * x[i] as int + m[0] as int * u_i as int, BASE) by {
                        assert cong(P_1[0] as int, y[0] as int * x[i] as int, BASE);
                        assert cong(P_2[0] as int, m[0] as int * u_i as int, BASE);
                        cong_add_lemma_2(P_1[0] as int, y[0] as int * x[i] as int, P_2[0] as int, m[0] as int * u_i as int, BASE);
                    }
                    cong_add_lemma_1(P_1[0] as int + P_2[0] as int, y[0] as int * x[i] as int + m[0] as int * u_i as int, A[0] as int, BASE);
                }
                cong_trans_lemma(A'[0] as int, P_1[0] as int + P_2[0] as int + A[0] as int, y[0] as int * x[i] as int + m[0] as int * u_i as int + A[0] as int, BASE);
            }
            cong(A'[0] as int, y[0] as int * x[i] as int + m[0] as int * u_i as int + A[0] as int, BASE);
            {
                assert u_i as int == ((A[0] as int + x[i] as int * y[0] as int) * m' as int) % BASE;
            }
            cong(A'[0] as int, y[0] as int * x[i] as int + m[0] as int * (((A[0] as int + x[i] as int * y[0] as int) * m' as int) % BASE) + A[0] as int, BASE);
            {
                assert cong(y[0] as int * x[i] as int + m[0] as int * (((A[0] as int + x[i] as int * y[0] as int) * m' as int) % BASE) + A[0] as int, 0, BASE) by {
                    mont_mul_div_aux_lemma_1(y[0] as int, x[i] as int, m[0] as int, A[0] as int , m' as int);
                }
                cong_trans_lemma(A'[0] as int, y[0] as int * x[i] as int + m[0] as int * (((A[0] as int + x[i] as int * y[0] as int) * m' as int) % BASE) + A[0] as int, 0, BASE);
            }
            cong(A'[0] as int, 0, BASE);
        }
        assert cong(A'[0] as int, 0, BASE);
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
                                cong_mul_lemma(power(BASE, n - 1), 0, A[n - 1] as int, BASE);
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
            mod_mod_lemma(seq_interp(m), BASE);
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
                cong_mul_lemma(seq_interp(m), m[0] as int, m' as int, BASE);
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
                    mul_mod_lemma(T[n-1] as int, power(BASE, n-1), BASE);
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

    lemma mont_mul_bounded_lemma(
        m: seq<uint32>,
        x: seq<uint32>,
        y: seq<uint32>,
        P_1: seq<uint32>,
        P_2: seq<uint32>,
        S: seq<uint32>,
        A: seq<uint32>,
        A': seq<uint32>,
        i: nat,
        u_i: uint32,
        m': uint32,
        n: nat)

        requires i < n;
        requires |m| == n && |x| == n && |y| == n;
        requires |A| == n + 2;
        requires |A'| == n + 3;

        requires seq_interp(A) < 2 * seq_interp(m) - 1;
        requires seq_interp(A) + seq_interp(S) == seq_interp(A');
        requires seq_interp(P_1) + seq_interp(P_2) == seq_interp(S);
        requires seq_interp(P_1) == seq_interp(y) * x [i] as int;
        requires seq_interp(P_2) == seq_interp(m) * u_i as int;

        requires 0 <= seq_interp(x) < seq_interp(m);
        requires 0 <= seq_interp(y) < seq_interp(m);

        requires cong(A'[0] as int, 0, BASE);

        ensures seq_interp(A'[1..n+2]) < 2 * seq_interp(m) - 1;
    {
        ghost var m_val := seq_interp(m);
        ghost var m_bound := m_val - 1;
        ghost var base_bound := BASE - 1;

        calc <= {
            seq_interp(A');
            seq_interp(A) + seq_interp(S);
            seq_interp(A) + seq_interp(P_1) + seq_interp(P_2);
            seq_interp(A) + seq_interp(y) * x [i] as int + seq_interp(P_2);
            {
                assert seq_interp(y) <= m_bound;
            }
            seq_interp(A) + m_bound * x [i] as int + seq_interp(P_2);
            {
                assert x [i] as int <= base_bound;
            }
            seq_interp(A) + m_bound * base_bound + seq_interp(P_2);
            seq_interp(A) + m_bound * base_bound + seq_interp(m) * u_i as int;
            {
                assert u_i as int <= base_bound;
            }
            seq_interp(A) + m_bound * base_bound + seq_interp(m) * base_bound;
            seq_interp(A) + m_bound * base_bound + m_val * base_bound;
        }

        calc ==> {
            seq_interp(A') < 2 * m_val - 1 + m_bound * base_bound + m_val * base_bound;
            seq_interp(A') < 2 * m_val - 1 + (m_val - 1) * base_bound + m_val * base_bound;
            seq_interp(A') < 2 * m_val - 1 + m_val * base_bound - base_bound + m_val * base_bound;
            seq_interp(A') < 2 * m_val - 1 + m_val * (BASE - 1) - (BASE - 1) + m_val * (BASE - 1);
            seq_interp(A') < 2 * m_val + m_val * (BASE - 1) - BASE + m_val * (BASE - 1);
            seq_interp(A') < 2 * m_val + m_val * BASE - m_val - BASE + m_val * (BASE - 1);
            seq_interp(A') < 2 * m_val + m_val * BASE - m_val - BASE + m_val * BASE - m_val;
            seq_interp(A') < m_val * BASE - BASE + m_val * BASE;
            seq_interp(A') < 2 * m_val * BASE - BASE;
            seq_interp(A') < BASE * (2 * m_val - 1);
            seq_interp(A') < BASE * (2 * seq_interp(m) - 1);
        }

        var T_1 := A'[1..];
    
        assert seq_interp(T_1) == seq_interp(A') / BASE by {
            seq_div_base_lemma(A', n + 3);
        }
        assert seq_interp(T_1) < 2 * seq_interp(m) - 1;

        var T_2 := T_1[..n+1];
        assert T_2 == A'[1..n+2];

        assert seq_interp(T_2) == seq_interp(T_1) by {
            assert seq_interp(T_1) < 2 * R(n) - 1 by {
                seq_interp_upper_bound_lemma(m, n);
            }
            msw_zero_lemma(T_1, n);
            zero_extend_lemma(T_2, n + 1, T_1, n + 2);
        }

        assert seq_interp(A'[1..n+2]) < 2 * seq_interp(m) - 1;
    }

    lemma mont_mul_congruent_lemma(
        m: seq<uint32>,
        x: seq<uint32>,
        y: seq<uint32>,
        P_1: seq<uint32>,
        P_2: seq<uint32>,
        S: seq<uint32>,
        A: seq<uint32>,
        A': seq<uint32>,
        i: nat,
        u_i: uint32,
        m': uint32,
        n: nat)

        requires i < n;
        requires |m| == n && |x| == n && |y| == n;
        requires |A| == n + 2;
        requires |A'| == n + 3;

        requires seq_interp(m) != 0;
        requires seq_interp(A) + seq_interp(S) == seq_interp(A');
        requires seq_interp(P_1) + seq_interp(P_2) == seq_interp(S);
        requires seq_interp(P_1) == seq_interp(y) * x [i] as int;
        requires seq_interp(P_2) == seq_interp(m) * u_i as int;

        requires seq_interp(A) == (seq_interp(x[..i]) * seq_interp(y) / power(BASE, i)) % seq_interp(m);
    {
        ghost var m_val := seq_interp(m);

        calc == {
            seq_interp(A') % m_val;
            (seq_interp(A) + seq_interp(S)) % m_val;
            (seq_interp(A) + seq_interp(P_1) + seq_interp(P_2)) % m_val;
            {
                assume false;
            }
            (seq_interp(A) + seq_interp(P_1)) % m_val;
            (seq_interp(A) + seq_interp(y) * x[i] as int) % m_val;
            ((seq_interp(x[..i]) * seq_interp(y) / power(BASE, i)) % m_val + seq_interp(y) * x[i] as int) % m_val;
            {
                assume false;
            }
            (seq_interp(x[..i]) * seq_interp(y) / power(BASE, i) + seq_interp(y) * x[i] as int) % m_val;
            {
                assume false;
            }
            (seq_interp(y) * seq_interp(x[..i]) / power(BASE, i) + seq_interp(y) * x[i] as int) % m_val;
            {
                assert power(BASE, i) / power(BASE, i) == 1;
            }
            (seq_interp(y) * seq_interp(x[..i]) / power(BASE, i) + seq_interp(y) * x[i] as int * (power(BASE, i) / power(BASE, i))) % m_val;
            {
                assume false;
            }
            ((seq_interp(y) * seq_interp(x[..i]) + seq_interp(y) * x[i] as int * power(BASE, i)) / power(BASE, i)) % m_val;
        }

    }

    method mont_mul(m: seq<uint32>, x: seq<uint32>, y: seq<uint32>, m': uint32, n: nat, ghost R: int)
        requires n > 2;
        requires |m| == n && |x| == n && |y| == n;
        requires R == power(BASE, n);
        requires cong(m' as int * seq_interp(m), -1, BASE);
        requires 0 <= seq_interp(x) < seq_interp(m); 
        requires 0 <= seq_interp(y) < seq_interp(m); 
    {
        var temp := new uint32[n + 1];
        var A :seq<uint32> := temp[..];
        assume seq_interp(A) == 0;
        var i := 0;

        assert seq_interp(A) == (seq_interp(x[..i]) * seq_interp(y) / power(BASE, i)) % seq_interp(m);

        while i < n
            decreases n - i;
            invariant |A| == n + 1;
            invariant seq_interp(A) < 2 * seq_interp(m) - 1;
            // invariant seq_interp(A) == (seq_interp(x[..i]) * seq_interp(y) * power(BASE_INV, i)) % seq_interp(m);
        {
            assume seq_interp(A) == (seq_interp(x[..i]) * seq_interp(y) / power(BASE, i)) % seq_interp(m);

            var u_i_ := ((A[0] as int + x[i] as int * y[0] as int) * m' as int) % BASE; 
            var u_i := u_i_ as uint32;

            var P_1 := magic_mul(y, x[i], n);
            var P_2 := magic_mul(m, u_i, n);
            var S := seq_add_c(P_1, P_2, n + 1);
            A := seq_zero_extend(A, n + 1, n + 2);
            var A' := seq_add_c(A, S, n + 2);

            assert cong(A'[0] as int, 0, BASE) by {
                mont_mul_divisible_lemma(m, x, y, P_1, P_2, S, A, A', i, u_i, m', n);
            }

            assert seq_interp(A'[1..n+2]) < 2 * seq_interp(m) - 1 by {
                mont_mul_bounded_lemma(m, x, y, P_1, P_2, S, A, A', i, u_i, m', n);
            }

            var A'' := A'[1..n+2];
            assume seq_interp(A'') == seq_interp(A') / BASE;

            i := i + 1;
            A := A'';
        }
    }

    method magic_mul(A: seq<uint32>, b: uint32, n: nat)
        returns (P: seq<uint32>)
        requires n != 0;
        requires |A| == n;
        ensures |P| == n + 1;
        ensures seq_interp(P) == seq_interp(A) * b as int;
        ensures cong(P[0] as int, A[0] as int * b as int, BASE);
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