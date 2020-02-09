module Divisible {

function method power(b:int, e:nat) : int
    decreases e;
{
    if (e==0) then
        1
    else
        b*power(b,e-1)
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

lemma {:induction k} divisible_by_five_lema(k: int)
	requires k >= 1;
	ensures (power(2, 3 * k) - power(3, k)) % 5 == 0;
{
	if k != 1 {
		calc == {
			(power(2, 3 * k) - power(3, k)) % 5;
			==
			(power(2, 3 * (k - 1) + 3) - power(3, (k - 1) + 1)) % 5;
			==
			{
				assert power(2, 3 * (k - 1) + 3) == (power(2, 3 * (k - 1)) * 8)
				by {
					exp_product_lema(2, 3 * (k - 1) + 3,  3 * (k - 1), 3);
				}
			}
			(power(2, 3 * (k - 1)) * 8 - power(3, (k - 1) + 1)) % 5;
			==
			{
				assert power(3, (k - 1) + 1) == (power(3, (k - 1)) * 3)
				by {
					exp_product_lema(3, 3 * (k - 1) + 1,  3 * (k - 1), 1);
				}
			}
			(power(2, 3 * (k - 1)) * 8 - power(3, (k - 1)) * 3) % 5;
			==
			(3 *(power(2, 3 * (k - 1)) - power(3, (k - 1))) + power(2, 3 * (k - 1)) * 5) % 5;
			==
			(3 *(power(2, 3 * (k - 1)) - power(3, (k - 1)))) % 5;
		}
	}
}

}

