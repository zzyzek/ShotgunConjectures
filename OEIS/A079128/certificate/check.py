# A079128: brute force over permutations (n <= 8) with "gcd of all cycle lengths = 1",
# compared with the entry's data; then, via cycle-type class sizes (n <= 60), checks
# gcd(a(n), n) = 1 and a(n) = (-1)^(m+1) (mod p) for every prime p | n, n = p m.
from itertools import permutations
from math import gcd, factorial
from functools import reduce
from sympy import primefactors
from sympy.utilities.iterables import partitions
data = [1, 1, 4, 15, 96, 455, 4320, 29295, 300160, 2663199, 36288000]
def cyc(p):
    seen=[0]*len(p); L=[]
    for i in range(len(p)):
        if not seen[i]:
            k=0; j=i
            while not seen[j]: seen[j]=1; j=p[j]; k+=1
            L.append(k)
    return L
for n in range(1, 9):
    c = sum(1 for p in permutations(range(n)) if reduce(gcd, cyc(p)) == 1)
    assert c == data[n-1], n
def a(n):
    tot=0
    for part in partitions(n):
        if reduce(gcd, part.keys()) != 1: continue
        z=1
        for k,mult in part.items(): z *= k**mult * factorial(mult)
        tot += factorial(n)//z
    return tot
for n in range(1, 61):
    v = a(n)
    if n <= 11: assert v == data[n-1]
    assert gcd(v, n) == 1, n
    for p in primefactors(n):
        m = n // p
        assert (v - (-1)**(m+1)) % p == 0, (n, p)
print("ok")
