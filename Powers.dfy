module Powers
{
    function method {:opaque} power(b:int, e:nat) : int
        decreases e;
    {
        if (e == 0) then 1
        else b * power(b, e - 1)
    }

    lemma {:induction e} power_base_one_lema(e: nat) 
        ensures power(1, e) == 1;
    {
        reveal power();
    }

    lemma {:induction e} power_add_one_lema(b:int, e:nat)
        ensures power(b, e) * b == power(b, e + 1);
    {
        reveal power();
    }

    lemma power_same_exp_lema(a: int, b: int, e: nat)
        ensures power(a, e) * power(b, e) == power(a * b, e);
    {
        assume false;
    }
}