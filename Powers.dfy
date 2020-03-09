module Powers
{
    function method {:opaque} power(b:int, e:nat) : int
        decreases e;
        ensures b > 0 ==> power(b, e) > 0;
    {
        if (e == 0) then 1
        else b * power(b, e - 1)
    }

    lemma {:induction e} power_base_one_lemma(e: nat) 
        ensures power(1, e) == 1;
    {
        reveal power();
    }

    lemma {:induction e} power_add_one_lemma(b:int, e:nat)
        ensures power(b, e) * b == power(b, e + 1);
    {
        reveal power();
    }

    lemma {:induction e} power_sub_one_lemma(b:int, e:nat)
        requires e != 0 && b != 0;
        ensures power(b, e) / b == power(b, e - 1);
    {
        assume false;
    }

    lemma power_same_exp_lemma(a: int, b: int, e: nat)
        ensures power(a, e) * power(b, e) == power(a * b, e);
    {
        assume false;
    }

    lemma power_mod_lemma(a: int, b: nat) 
        ensures (b != 0 && a != 0) ==> (power(a, b) % a == 0);
}