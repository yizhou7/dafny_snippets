import Crypto.Util.number
import Crypto.Random

import sys

R = 2 **32
B = 2 **32

def mod_inverse(a, m) : 
    m0 = m 
    y = 0
    x = 1
  
    if (m == 1) : 
        return 0
    while (a > 1) : 
        # q is quotient 
        q = a // m 
        t = m 
        # m is remainder now, process 
        # same as Euclid's algo 
        m = a % m 
        a = t 
        t = y 
        # Update x and y 
        y = x - q * y 
        x = t 
    # Make x positive 
    if (x < 0) : 
        x = x + m0 
  
    return x 

def compute_rr(n):
    return R * R % n

def generate_valid_n():
    bits=16

    while True:
        # print ("No of bits in prime is ",bits)
        p=Crypto.Util.number.getPrime(bits, randfunc=Crypto.Random.get_random_bytes)
        # print ("\nRandom n-bit Prime (p): ",p)

        q=Crypto.Util.number.getPrime(bits, randfunc=Crypto.Random.get_random_bytes)
        # print ("\nRandom n-bit Prime (q): ",q)
        n = p * q
        if n % 3 != 0:
            return n

while True:
    n = generate_valid_n()
    rr = compute_rr(n)

    n_R = n/R
    rr_n = rr/n

    if 0.47 < n_R < 0.5 and rr_n > 0.8:
        print("n/R:", n_R)
        print("rr/n:", rr_n)

        n0inv = B - mod_inverse(n, B)

        out = f"""
            key->n[0] = {hex(n)};
            key->n0inv = {hex(n0inv)}; // key.n0inv * key.n[0] == -1 mod b
            key->rr[0] = {hex(rr)}; // key.rr == R * R % key.n
        """
        print(out)