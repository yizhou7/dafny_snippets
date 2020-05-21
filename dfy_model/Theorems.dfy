// include "NativeTypes.dfy"
include "Powers.dfy"
include "Congruences.dfy"

module Theorems
{
    import opened Congruences
    import opened Powers

    predicate {:opaque} coprime(a: nat, b: nat)
    predicate {:opaque} prime(a: nat)
    	ensures a >= 3;

    lemma cong_k_exist_lemma(a: int, b: int, n: int)
        requires n != 0;
    	requires cong(a, b, n);
    	ensures exists k :int :: a - b == n * k;

	lemma power_power_lemma(b: int, e1: nat, e2: nat)
        ensures power(power(b, e1), e2) == power(b, e1 * e2);

    lemma power_mod_lemma_2(b: int, e: nat, n: int)
        requires n != 0;
        ensures power(b % n, e) % n == power(b, e) % n;

    lemma fermats_little_theorem(a: int, p: nat)
    	requires prime(p) && !cong(a, 0, p);
    	ensures cong(power(a, p - 1), 1, p);

    lemma chinese_remainder_theorem(a: int, b: int, p: nat, q: nat)
        requires prime(p) && prime(q);
        requires cong(a, b, p) ;
        requires cong(a, b, q);
        ensures  cong(a, b, p * q);
}