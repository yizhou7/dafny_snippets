// include "NativeTypes.dfy"
include "Powers.dfy"
include "Congruences.dfy"

module Theorems
{
    import opened Congruences
    import opened Powers

    predicate {:opaque} coprime(a: int, b: int)
    predicate {:opaque} prime(a: int)

	lemma power_power_lemma(b: int, e1: nat, e2: nat)
        ensures power(power(b, e1), e2) == power(b, e1 * e2);

    lemma power_mod_lemma_2(b: int, e: nat, n: int)
        ensures power(b % n, e) % n == power(b, e) % n;

    lemma fermats_little_theorem(a: int, p: int)
    	requires prime(p);
    	ensures cong(power(a, p - 1), 1, p); 
}