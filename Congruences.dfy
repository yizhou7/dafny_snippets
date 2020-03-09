module Congruences {
    predicate {:opaque} cong(a: int, b: int, n: int)
        requires n != 0;
    {
        a % n == b % n
    }

    lemma cong_trans_lemma(a: int, b: int, c: int, n: int)
        requires n != 0;
        requires cong(a, b, n) && cong(b, c, n);
        ensures cong(a, c, n);
    {
        reveal cong();
    }

    lemma cong_equiv_lemma(a: int, b: int, n: int)
        requires n != 0;
        ensures cong(a, b, n) == ((a - b) % n == 0);
    {
        reveal cong();
        assume (a % n == b % n) ==> ((a - b) % n == 0);
        assume (a % n == b % n) <== ((a - b) % n == 0);
    }

    lemma cong_residual_lemma(a: int, b: nat, n: nat)
        requires n != 0;
        ensures (cong(a, b, n) && b < n) == (b == a % n);
    {
        reveal cong();        
    }

    lemma mul_mod_lemma(a: int, n: int)
        requires n != 0;
        ensures a * n % n == 0;
    {
        assume false;
    }

    lemma mod_mod_lemma(a: int, n: int)
        requires n != 0;
        ensures cong((a % n), a, n);
    {
        reveal cong();
    }

    lemma cong_mul_lemma(a: int, b: int, c: int, n: int)
        requires n != 0;
        requires cong(a, b, n);
        ensures cong(a * c, b * c, n);
    {
        assume false;
        // ghost var k1 := a / n;
        // ghost var k2 := b / n;
        // assert k1 * n + a % n == a;
        // assert k2 * n + b % n == b;
        // calc == {
        //     (a * c - b * c) % n;
        //     ((k1 * n + a % n - k2 * n - b % n) * c) % n;
        //     ((k1 * n - k2 * n) * c) % n;
        //     ((k1 - k2 ) * c * n) % n;
        //     {
        //         mul_mod_lemma((k1 - k2 ) * c, n);
        //     }
        //     0;
        // }
        // assert (a * c) % n == (b * c) % n by {
        //     assert (a * c - b * c) % n == 0;
        //     cong_equiv(a * c, b * c, n);
        // }
        // assert (a * c) % n == (b * c) % n;
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
}
