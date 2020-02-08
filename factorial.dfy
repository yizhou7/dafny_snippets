module Factorial {

function factorial_spec (n: int) : int
	decreases n;
	requires n >= 0;
{
	if n == 0 then 1 else n * factorial_spec (n - 1)
}

lemma {:induction n} factorial_step(n: int)
	requires n >= 0;
	ensures factorial_spec(n + 1) == factorial_spec(n) * (n + 1)
{

}

method factorial_impl(n: int)
	returns (x: int)
	requires n >= 0;
{
	var result, i := 1, 1;
	assert result == factorial_spec(i);

	while i <= n
		decreases n - i;
		invariant result == factorial_spec(i);
	{
		var i' := i + 1;
		var result' := result * i';

		calc {
			result'; 
		==
			factorial_spec(i) * (i + 1);
		==
			{ 
				factorial_step(i);
			}
			factorial_spec(i + 1);
		}

		result := result';
		i := i';

		assert result == factorial_spec(i);
	}
}

}

