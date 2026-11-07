# Independent check of witness lists: palindrome, digit set, digit sum = prime(n), and
# strong probable prime to 8 fixed bases (the proofs/BPSW are from PARI).
import sys, random
A, allowed = sys.argv[1], set(sys.argv[2])
def primes(k):
    P, x = [], 2
    while len(P) < k:
        if all(x % p for p in P if p * p <= x): P.append(x)
        x += 1
    return P
P = primes(400)
def sprp(n, a):
    d, s = n - 1, 0
    while d % 2 == 0: d //= 2; s += 1
    x = pow(a, d, n)
    if x in (1, n - 1): return True
    for _ in range(s - 1):
        x = x * x % n
        if x == n - 1: return True
    return False
for line in open(f"witnesses_{A}.txt"):
    n, p, L, kind, w = line.split()
    n, p = int(n), int(p)
    assert P[n - 1] == p and w == w[::-1] and set(w) <= allowed and sum(map(int, w)) == p and len(w) == int(L)
    N = int(w)
    assert all(sprp(N, a) for a in (2, 3, 5, 7, 11, 13, 17, 19)), n
print(A, "ok")
