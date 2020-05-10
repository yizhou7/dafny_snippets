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

n = int(sys.argv[1], 16)
print("n/R:", n/R)
rr = compute_rr(n) 
# print("rr/R:", rr/R)

n0inv = B - mod_inverse(n, B)

out = f"""
    key.n[0] = {hex(n)};
    key.n0inv = {hex(n0inv)}; // key.n0inv * key.n[0] == -1 mod b
    key.rr[0] = {hex(rr)}; // key.rr == R * R % key.n
"""

print(out )