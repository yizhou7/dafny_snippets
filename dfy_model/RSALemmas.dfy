include "NativeTypes.dfy"
include "SeqInt.dfy"
include "Powers.dfy"
include "Congruences.dfy"

module RSALemmas
{
    import opened Congruences
    import opened SeqInt
    import opened Powers
    import opened NativeTypes

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

    datatype pub_key = pub_key(
        e: nat, 
        m: seq<uint32>,
        RR: seq<uint32>,
        m': uint32,
        len: nat,
        n_val: int,
        BASE_INV: nat,
        R: nat,
        R_INV: nat
    )

    predicate valid_pub_key(key: pub_key) {
        && key.e == 3
        && |key.m| == |key.RR| == key.len >= 1
        && seq_interp(key.m) == key.n_val
        && 0 != key.n_val < power(BASE, key.len)
        && cong(key.m' as nat * key.m[0] as nat, -1, BASE)
        && cong(BASE * key.BASE_INV, 1, key.n_val)
        && key.R == power(BASE, key.len)
        && key.R_INV == power(key.BASE_INV, key.len)
        && cong(key.R_INV * key.R, 1, key.n_val)
        && 0 <= seq_interp(key.RR) < key.n_val
        && cong(seq_interp(key.RR), key.R * key.R, key.n_val)
    }

    datatype rsa_params = rsa_params(
        e: nat,
        d: nat,
        p: nat,
        q: nat,
        phi: nat,
        n: nat)

    predicate rsa_valid(rsa: rsa_params) 
    {
        && prime(rsa.p)
        && prime(rsa.q)
        && rsa.p * rsa.q == rsa.n
        && rsa.phi == (rsa.q - 1) * (rsa.p - 1)
        && coprime(rsa.phi, rsa.e)
        && 0 < rsa.d < rsa.phi
        && 0 < rsa.e < rsa.phi
        && cong(rsa.e * rsa.d, 1, rsa.phi)
    }

    lemma rsa_cong_lemma(rsa: rsa_params, m: nat, p: nat)
        requires rsa_valid(rsa);
        requires p == rsa.p || p == rsa.q;
    {
        var e, d := rsa.e, rsa.d;
        var q := if p == rsa.q then rsa.p else rsa.q;
        var n, phi := rsa.n, rsa.phi;

    }

    lemma rsa_correct_lemma(rsa: rsa_params, m: nat)
        requires rsa_valid(rsa);
        ensures cong(power(m, rsa.e * rsa.d), m, rsa.n);
    {
    //     var e, d := rsa.e, rsa.d;
    //     var p, q := rsa.p, rsa.q;
    //     var n, phi := rsa.n, rsa.phi;

    }

    // {
    //     var c' := power(m, d) % n;

    //     calc == {
    //         power(c', e) % n;
    //         power(power(m, d) % n, e) % n;
    //         {
    //             power_mod_lemma_2(power(m, d), e, n);
    //         }
    //         power(power(m, d), e) % n;
    //         {
    //             power_power_lemma(m, d, e);
    //         }
    //         power(m, d * e) % n;
    //     }

    //     assert exists k :int :: (d * e == phi * k + 1) by {
    //         assert cong(d * e, 1, phi);
    //         cong_k_exist_lemma(d * e, 1, phi);
    //     }

    //     var k :| d * e == phi * k + 1;

    //     assert cong(power(m, d * e), m, n) by {
    //         ghost var temp := power(m, d * e);
    //         assert cong(temp, m, q) by {
    //             rsa_cong_lemma_1(rsa, key, m, c, k, q);
    //         }
    //         assert cong(temp, m, p) by {
    //             rsa_cong_lemma_1(rsa, key, m, c, k, p);
    //         }
    //         chinese_remainder_theorem(temp, m, p, q);
    //     }
    // }
}

/*
    lemma rsa_cong_lemma_2(rsa: rsa_params, key: pub_key, m: nat, c: nat, k: int, p: nat)
        requires rsa.d_val * key.e == rsa.phi_val * k + 1;
        requires rsa_valid(rsa, key);
        requires power(c, key.e) % key.n_val == m;
        requires p == rsa.p_val || p == rsa.q_val;
        requires cong(m, 0, p);
        ensures cong(power(m, rsa.d_val * key.e), m, p);        
    {
        var d := rsa.d_val;
        var e := key.e;

        ghost var temp := power(m, d * e);
        assert cong(m, 0, p);

        calc ==> {
            cong(m, 0, p);
            {
                cong_power_lemma(m, 0, d * e, p);
            }
            cong(temp, power(0, d * e), p);
            cong(temp, 0, p);
            {
                assert cong(m, 0, p);
                cong_trans_lemma(temp, 0, m, p);
            }
            cong(temp, m, p);
        }
        assert cong(power(m, d * e), m, p);
    }

    lemma rsa_cong_lemma_3(rsa: rsa_params, key: pub_key, m: nat, c: nat, k: int, p: nat)
        requires rsa.d_val * key.e == rsa.phi_val * k + 1;
        requires rsa_valid(rsa, key);
        requires power(c, key.e) % key.n_val == m;
        requires p == rsa.p_val || p == rsa.q_val;
        // ensures cong(power(m, rsa.d_val * key.e), m, p);
    {
        var d := rsa.d_val;
        var n := key.n_val;
        var e := key.e;
        var phi := rsa.phi_val;
        var q := if p == rsa.p_val then rsa.q_val else rsa.p_val;

        assert prime(p);
        calc ==> {
            prime(p);
            {
                assume !cong(m, 0, p);
                fermats_little_theorem(m, p);
            }
            cong(power(m, p - 1), 1, p); 
            {
                cong_power_lemma(power(m, p - 1), 1, (q - 1) * k, p);
            }
            cong(power(power(m, p - 1), (q - 1) * k), power(1, (q - 1) * k), p);
            {
                power_base_one_lemma((q - 1) * k);
            }
            cong(power(power(m, p - 1), (q - 1) * k), 1, p);
            {
                power_power_lemma(m, (p - 1), (q - 1) * k);
            }            
            cong(power(m, (p - 1) * (q - 1) * k), 1, p);
            {
                assert (q - 1) * (p - 1) == phi;
            }
            // cong(power(m, phi * k), 1, p);
            // {
            //     cong_mul_lemma_1(power(m, phi * k), 1, m, p);
            // }
            // cong(power(m, phi * k) * m, m, p);
            // {
            //     power_add_one_lemma(m, phi * k);
            // }
            // cong(power(m, phi * k + 1), m, p);
            // {
            //     assert d * e == phi * k + 1;
            // }
            // cong(power(m, d * e), m, p);
        }
    }

    lemma rsa_cong_lemma_1(rsa: rsa_params, key: pub_key, m: nat, c: nat, k: int, target: nat)
        requires rsa.d_val * key.e == rsa.phi_val * k + 1;
        requires rsa_valid(rsa, key);
        requires cong(power(c, key.e), m, key.n_val);
        requires target == rsa.p_val || target == rsa.q_val;
        ensures cong(power(m, rsa.d_val * key.e), m, target);
    {
        var d := rsa.d_val;
        var n := key.n_val;
        var e := key.e;
        var p := target;

        if cong(m, 0, p) {
            rsa_cong_lemma_2(rsa, key, m, c, k, p);
        }  else {
            // assert cong(power(m, d * e), m, p);
            assume false;
        }
    }

    lemma rsa_signature_lemma(rsa: rsa_params, key: pub_key, m: nat, c: nat)
        requires rsa_valid(rsa, key);
        requires cong(power(c, key.e), m, key.n_val);
        // ensures cong(c, power(m, d), n);
    {


        ghost var d';
        if cong(c, power(m, d'), n) && d' != d {
            assert cong(power(c, e), power(m, d * e), n) by {
                cong_trans_lemma(power(c, e), m, power(m, d * e), n);
            }
            assume cong(power(c, e), power(m, d' * e), n);

        }
    }
*/