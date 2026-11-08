# Conjecture 1 check for A227864: every n >= 2, n != 4, has a base b >= 2
# in which the digit reversal of n is prime.  Also the restricted version
# (gcd(b, n) = 1) for n = 6k +- 1.  Usage: python3 search.py N
import sys
def isprime(n):
    if n < 2: return False
    for p in (2,3,5,7,11,13,17,19,23,29,31,37):
        if n % p == 0: return n == p
    d, s = n - 1, 0
    while d % 2 == 0: d //= 2; s += 1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        x = pow(a, d, n)
        if x in (1, n - 1): continue
        for _ in range(s - 1):
            x = x * x % n
            if x == n - 1: break
        else: return False
    return True
def rev(b, n):
    r = 0
    while n: r = r * b + n % b; n //= b
    return r
from math import gcd
N = int(sys.argv[1]); maxa = (0, 0); maxc = (0, 0); fails = []; failsc = []
for n in range(2, N + 1):
    if n == 4: continue
    a = next((b for b in range(2, n + 2) if isprime(rev(b, n))), 0)
    if a == 0: fails.append(n)
    if n != 2 and a > maxa[0]: maxa = (a, n)
    if n % 6 in (1, 5) and n > 1:
        c = next((b for b in range(2, n + 2) if gcd(b, n) == 1 and isprime(rev(b, n))), 0)
        if c == 0: failsc.append(n)
        if not isprime(n) and c > maxc[0]: maxc = (c, n)
print("N", N, "conj1 failures", fails[:10], "max a(n) (n != 2)", maxa)
print("restricted: 6k+-1 failures", failsc[:10], "max over composite 6k+-1", maxc)
