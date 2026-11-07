# JRM generalisation of A084189: composite palindromes N <= X all of whose prime
# factors (with multiplicity) are palindromic primes with every digit >= 4.
# Enumerates products of such primes (any number of factors) up to X.
import sys
from itertools import product
X = int(sys.argv[1])
def isprime(n):
    if n < 2:
        return False
    for p in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        if n % p == 0:
            return n == p
    d, s = n - 1, 0
    while d % 2 == 0:
        d //= 2; s += 1
    for a in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        x = pow(a, d, n)
        if x in (1, n - 1):
            continue
        for _ in range(s - 1):
            x = x * x % n
            if x == n - 1:
                break
        else:
            return False
    return True
P = [5, 7]
for half in range(1, (len(str(X)) + 1) // 2):
    for t in product('456789', repeat=half):
        s = ''.join(t)
        for m in '456789':
            v = int(s + m + s[::-1])
            if v <= X // 5 and isprime(v):
                P.append(v)
P.sort()
print("palindromic primes with digits >= 4 up to X/5:", len(P))
out = []
def rec(i, n, k):
    if k >= 2:
        s = str(n)
        if s == s[::-1]:
            out.append(n)
    for j in range(i, len(P)):
        if n * P[j] > X:
            break
        rec(j, n * P[j], k + 1)
rec(0, 1, 0)
for n in sorted(out):
    print(n)
