include "Powers.dfy"

module NaiveMont {
    import opened Powers

    predicate congruent_def(a: int, b: int, n: int)
        requires n != 0;
    {
        a % n == b % n
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

    method montgomery_product(A: nat, B: nat, N:nat, R: nat, R_inv: nat) returns (P: nat)
        requires 0 < N < R && gcd_def(N, R, 1);
        requires R_inv == mod_inverse(R, N);
        // requires congruent_def(N' * N, -1, R);
        ensures P == A * B * R_inv % N;
    {
        var N_inv := mod_inverse(N, R);
        var N';
        assume(congruent_def(N' * N_inv, R - 1, R));

        var T := A * B;
        var M := T * N' % R;
        P := (T + M * N) / R;

        assume false;
    }




}