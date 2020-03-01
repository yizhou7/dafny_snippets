include "Powers.dfy"

module NaiveMont {
    import opened Powers

    predicate cong(a: int, b: int, n: int)
        requires n != 0;
    {
        a % n == b % n
    }

    lemma cong_equiv(a: int, b: int, n: int)
        requires n != 0;
        ensures (a % n == b % n) == ((a - b) % n == 0);
    {
        assume (a % n == b % n) ==> ((a - b) % n == 0);
        assume (a % n == b % n) <== ((a - b) % n == 0);
    }

    lemma mul_mod_lemma(a: int, n: int)
        requires n != 0;
        ensures a * n % n == 0;
    {
        assume false;
    }

    lemma cong_mul_lemma(a: int, b: int, c: int, n: int)
        requires n != 0;
        requires a % n == b % n;
        ensures a * c % n == b * c % n;
    {
        ghost var k1 := a / n;
        ghost var k2 := b / n;
        assert k1 * n + a % n == a;
        assert k2 * n + b % n == b;
        calc == {
            (a * c - b * c) % n;
            ((k1 * n + a % n - k2 * n - b % n) * c) % n;
            ((k1 * n - k2 * n) * c) % n;
            ((k1 - k2 ) * c * n) % n;
            {
                mul_mod_lemma((k1 - k2 ) * c, n);
            }
            0;
        }
        assert a * c % n == b * c % n by {
            assert (a * c - b * c) % n == 0;
            cong_equiv(a * c, b * c, n);
        }
        assert a * c % n == b * c % n;
    }

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

    // lemma mont_divisibility(T: nat, )

    method mont_mul(A: nat, B: nat, N:nat, N_inv: nat, N':nat, R: nat, R_inv: nat) returns (P: nat)
        requires 0 < N < R && gcd_def(N, R, 1);
        // requires R_inv == mod_inverse(R, N);
        requires N_inv == mod_inverse(N, R);
        requires cong(N' * N, -1, R);
        // ensures P == A * B * R_inv % N;
    {
        var T := A * B;
        var M := T * N' % R;

        assert cong(T * N' % R, T * N', R);

        calc ==> {
            cong(T * N' % R, T * N', R);
            // cong(T * N' % R * N, T * N' * N, R);
        }
        // calc == {
        //     (T + M * N) % R;
        //     (T + (T * N' % R) * N) % R;

        // }

        assume ((T + M * N) % R == 0);
        P := (T + M * N) / R;

        // assume false;
    }

}