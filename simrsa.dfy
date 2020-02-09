module SIMRSA {

function method power(b:int, e:nat) : int
    decreases e;
{
    if (e == 0) then 1
    else b * power(b ,e - 1)
}

lemma {:induction e} exp_one_rule_lema(e: nat)
    ensures power(1, e) == 1;
{
    assert true;
}

lemma {:induction e, e_1} exp_product_lema(b:int, e:nat, e_1:nat, e_2:nat)
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

lemma {:induction e, e_2} exp_power_lema_1(b:int, e: nat, e_1:nat, e_2:nat)
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
                    exp_one_rule_lema(e_2);
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
                    exp_product_lema(b, e_1 * e_2, e_1 * (e_2 - 1), e_1);
                }
                power(b, e_1 * (e_2 - 1)) *  power(b, e_1);
                ==
                {
                    exp_power_lema_1(b, e_1 * (e_2 - 1), e_1, e_2 -1);
                }
                power(power(b, e_1), e_2 - 1) *  power(b, e_1);
                ==
                {
                    exp_product_lema(power(b, e_1), e_2, e_2 - 1, 1);
                }
                power(power(b, e_1), e_2);
            }
        }
    }
}
lemma {:induction e} mod_exp_sub_one_lema(b: int, e: nat, m: nat)
    requires e >=1 && m >= 2;
    ensures power(b, e) % m == ((power(b, e - 1) % m) * (b % m)) % m
{
    if e == 0 {
        assert true;
    } else {
        assume false;
    }
}
lemma {:induction e} mod_exp_lema(b: int, e: nat, m: nat)
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

