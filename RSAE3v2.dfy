include "NativeTypes.dfy"
include "Powers.dfy"
include "Congruences.dfy"
include "SeqInt.dfy"

module RSAE3v2 {
    import opened NativeTypes
    import opened Powers
    import opened Congruences
    import opened SeqInt

    method compact_mont_mul(m: seq<uint32>, x: seq<uint32>, y: seq<uint32>, m': uint32, n: nat, ghost R: int, ghost BASE_INV: nat)
        returns (A: seq<uint32>)

        requires n > 2;
        requires |m| == n && |x| == n && |y| == n;
        requires R == power(BASE, n);
        requires cong(m' as int * seq_interp(m), -1, BASE);
        requires 0 <= seq_interp(x) < seq_interp(m); 
        requires 0 <= seq_interp(y) < seq_interp(m); 
        requires cong(BASE * BASE_INV, 1, seq_interp(m));

        // ensures seq_interp(A) == (seq_interp(x) * seq_interp(y) * power(BASE_INV, n)) % seq_interp(m);
    {
        A  := zero_seq_int(n + 1);
        assert seq_interp(A) == 0;

        ghost var m_val := seq_interp(m);
        ghost var y_val := seq_interp(y);

        var i := 0;
        
        while i < n
            decreases n - i;
            // invariant |A| == n + 1;
        {
            A := compact_mont_mul_add(m, A, x[i], y, m', n);
            i := i + 1;
        }
    }

    method compact_mont_mul_add(m: seq<uint32>, A: seq<uint32>, x_i: uint32, y: seq<uint32>, m': uint32, n: nat)
        returns (A'': seq<uint32>)
    {
        var u_i_ := ((A[0] as int + x_i as int * y[0] as int) * m' as int) % BASE; 
        var u_i := u_i_ as uint32;

        var P_1 := magic_mul(y, x_i, n);
        var P_2 := magic_mul(m, u_i, n);
        var S := seq_add_c(P_1, P_2, n + 1);

        var A := seq_zero_extend(A, n + 1, n + 2);
        var A' := seq_add_c(A, S, n + 2);
        A'' := A'[1..n+2];
    }

    method magic_mul(A: seq<uint32>, b: uint32, n: nat)
        returns (P: seq<uint32>)
        requires n != 0;
        requires |A| == n;
        ensures |P| == n + 1;
    {
        var temp := new uint32[n + 1];
        temp[0] := 0;
        P := temp[..];

        assert P[0] == 0;

        var i := 0;
        var c :uint32 := 0;

        while i < n 
            decreases n - i;
            invariant |A| == n;
            invariant |P| == n + 1;
            invariant i < |P|;
        {
            var product :uint64 := A[i] as uint64 * b as uint64 + c as uint64;
            var lower, upper := split64(product);

            assert lower as int + upper as int  * BASE == product as int;

            P := P[i := lower];

            i := i + 1;
            c := upper;
        }
    
        P := P[n := c];
    }
}