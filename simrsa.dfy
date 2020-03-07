module SIMRSA {

function method power(b:int, e:nat) : int
    decreases e;
{
    if (e == 0) then 1
    else b * power(b ,e - 1)
}

lemma {:induction e} exp_one_rule_lemma(e: nat)
    ensures power(1, e) == 1;
{
    assert true;
}

lemma {:induction e, e_1} exp_product_lemma(b:int, e:nat, e_1:nat, e_2:nat)
	requires e_1 + e_2 == e; 
	ensures power(b, e) == power(b, e_1) * power(b, e_2)
{
	if e_1 == 0 {
		assert true;
	} else {
		assert power(b, e_1) == b * power(b, e_1 - 1);
		assert power(b, e - 1) ==  power(b, e_1 - 1) * power(b, e_2);
	}
}

lemma {:induction e, e_2} exp_power_lemma_1(b:int, e: nat, e_1:nat, e_2:nat)
    decreases e, e_2;
    requires e == e_1 * e_2
    ensures power(b, e) == power(power(b, e_1), e_2)
{
    if e_2 == 0 {
        assert true;
    } else {
        if e_1 == 0 {
            assert e == 0;
            calc == {
                power(power(b, e_1), e_2);
                ==
                power(power(b, 0), e_2);
                ==
                power(1, e_2);
                ==
                {
                    exp_one_rule_lemma(e_2);
                }
                1;
            }
        } else {
            calc == {
                power(b, e);
                ==
                power(b, e_1 * e_2);
                ==
                {
                    exp_product_lemma(b, e_1 * e_2, e_1 * (e_2 - 1), e_1);
                }
                power(b, e_1 * (e_2 - 1)) *  power(b, e_1);
                ==
                {
                    exp_power_lemma_1(b, e_1 * (e_2 - 1), e_1, e_2 -1);
                }
                power(power(b, e_1), e_2 - 1) *  power(b, e_1);
                ==
                {
                    exp_product_lemma(power(b, e_1), e_2, e_2 - 1, 1);
                }
                power(power(b, e_1), e_2);
            }
        }
    }
}

predicate congruent_def(a: int, b: int, n: int)
{
    exists k : int :: a - b == n * k
}


lemma mul_distrubtive_lemma(n: int, a: int, b: int, c: int)
    ensures n * (a + b + c) == n * a + n * b  + n * c;
{
    assert true;
}

lemma mod_mul_lemma(a_1: int, a_2: int, b_1: int, b_2: int, n: int)
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
            assert n * n * k_1 * k_2 == n * (n * k_1 * k_2); // order of these asserts somehow matter
        }
        n * (n * k_1 * k_2) + n * (b_1 * k_2) + n * (k_1 * b_2);
        ==
        {
            mul_distrubtive_lemma(n, n * k_1 * k_2, b_1 * k_2, k_1 * b_2);
        }
        n * (n * k_1 * k_2 + b_1 * k_2 + k_1 * b_2);
    }
    ghost var k := n * k_1 * k_2 + b_1 * k_2 + k_1 * b_2;
    assert a_1 * a_2 - b_1 * b_2 == n * k;
    assert congruent_def(a_1 * a_2, b_1 * b_2, n);
}

lemma {:induction e} mod_exp_lemma(b: int, e: nat, m: nat)
    requires m >= 2;
    ensures power(b, e) % m == (power(b % m , e)) % m
{
    if e == 0 {
        assert true;
    } else {
        assert power(b, e - 1) % m == (power(b % m , e - 1)) % m;
        assume false;
    }
}

predicate divides_def(d:nat, n:int)
    requires d != 0;
{
    (n % d) == 0
}

// predicate is_gcd(a:nat, b:nat, gcd:nat)
// {
//     gcd != 0
//     && divides(gcd,a)
//     && divides(gcd,b)
//     && forall x:int :: gcd<x ==> !(divides(x,a) && divides(x,b))
// }

predicate prime_def(n:nat)
{
    forall cf:nat :: 2 <= cf < n ==> !divides_def(cf, n)
}

method encrypt_decrypt()
{
    var p, q := 17, 19;
    var n := p * q;
    var t := (p - 1) * (q - 1);
    var e, d := 7, 247;

    var message_plain := 42;
    var message_cipher := power(message_plain, e) % n;
    var message_plain' := power(message_cipher, d) % n;
    calc == {
        message_plain';
        ==
        power(power(message_plain, e) % n, d) % n;
        // ==
        // {
            
        // }
        // (power(message_plain, d * e) % n) % n;
    }

    // assert message_plain == message_plain';
}

}

