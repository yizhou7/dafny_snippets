module SIMRSA {

function method power(b:int, e:nat) : int
    decreases e;
{
    if (e==0) then
        1
    else
        b*power(b,e-1)
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

    assert message_plain == message_plain';
}

}

