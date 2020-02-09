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

}

lemma {:induction e, e_2} exp_power_rule_1(b:int, e: nat, e_1:nat, e_2:nat)
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
            assert e_2 >= 1;
            assert e >= 1;
            // assert power(b, e -1) == power(power(b, e_1), e_2 - 1);

            assume false;
        }
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
    }

    // assert message_plain == message_plain';
}

}

