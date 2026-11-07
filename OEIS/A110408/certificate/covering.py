# For n with no PRP N_k (k <= 400) in search.out, test for a covering congruence:
# primes q < 2000 (q not dividing 10) with ord_q(10^d) | P, P = 720 (d-digit n);
# N_k mod q is periodic in k with period ord_q(10^d) (geometric sum; q = 3, 11 handled
# by computing N_k mod q directly over one period P*q). Reports n where every k in
# [1, P] has some q | N_k with N_k > q.
import sys
from math import gcd
def rev(n): return int(str(n)[::-1])
miss = eval(open("search.out").read().split(": ")[1].split("\n")[0].replace("List(", "").rstrip(")"))
primes = [q for q in range(2, 2000) if all(q % r for r in range(2, int(q**0.5) + 1)) and q not in (2, 5)]
def Nmod(r, n, d, k, q):
    B = pow(10, d, q); R = 0
    for _ in range(k): R = (R * B + r) % q
    return (R * B + n) % q
found = []
for P in (720, 5040):
    for n in miss:
        d = len(str(n)); r = rev(n)
        cover = [False] * (P + 1)
        for q in primes:
            # period of N_k mod q divides q * ord; test whether it divides P via direct check
            B = pow(10, d, q); o = 1; x = B
            while x != 1: x = x * B % q; o += 1
            per = o if (B - 1) % q else q
            if P % per: continue
            R = 0
            for k in range(1, P + 1):
                R = (R * B + r) % q
                if (R * B + n) % q == 0: cover[k] = True
        if all(cover[1:]): found.append((n, P))
    print("P =", P, "covered n:", [f for f in found if f[1] == P])
