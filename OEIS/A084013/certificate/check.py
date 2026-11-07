# A084013 / A084015 checks.
# (1) Brute force: least and greatest n-digit admissible multiples of n for n <= 10 reproduce the data
#     (admissible: palindrome; for n = 10^s n', 10 not dividing n', N = 10^s u with u a palindrome).
# (2) The construction of A084013_mathlib.lean, built explicitly for n <= 400: has n digits, is a
#     multiple of n, and is admissible.
from math import gcd
def pal(x):
    s = str(x); return s == s[::-1]
def adm(N, n):
    if n % 10:
        return pal(N)
    nn = n
    while nn % 10 == 0:
        if N % 10:
            return False
        N //= 10; nn //= 10
    return pal(N)
A084013 = [1,22,111,2112,50005,201102,1002001,21100112,100070001,1000000010]
A084015 = [9,88,999,8888,59995,897798,9994999,88899888,999999999,9999999990]
for n in range(1, 11):
    lo, hi = 10 ** (n - 1), 10 ** n
    first = next(N for N in range(((lo + n - 1) // n) * n, hi, n) if adm(N, n))
    last = next(N for N in range((hi - 1) // n * n, lo - 1, -n) if adm(N, n))
    assert first == A084013[n - 1] and last == A084015[n - 1], (n, first, last)
print("(1) data n <= 10 reproduced")
def phi(m):
    return sum(1 for k in range(1, m + 1) if gcd(k, m) == 1)
def ord_r(m):
    # r = 3^k phi(m') with m = 3^k m', as in ord_bound
    k, mm = 0, m
    while mm % 3 == 0:
        mm //= 3; k += 1
    return 3 ** k * phi(mm)
def pal_U(m, L):
    r = ord_r(m)
    assert 1 <= r <= L and (10 ** r - 1) % (9 * m) == 0
    U = (10 ** r - 1) // 9
    return U * (10 ** (L - r) + 1)
def pal_G(g, m, e, L):
    R = e * phi(m)
    Gp = str(g).zfill(e)[::-1]
    lo = [int(c) for c in Gp] + [9] * (R - e) + [9 - int(c) for c in Gp]
    W = lo + [0] * (L - 2 * (R + e)) + lo[::-1]
    return int(''.join(map(str, W[::-1])))
def pal_exists(n, L):
    a = b = 0; m = n
    while m % 2 == 0: m //= 2; a += 1
    while m % 5 == 0: m //= 5; b += 1
    if a + b == 0:
        return pal_U(m, L)
    return pal_G(2 ** a * 5 ** b, m, a + b, L)
for n in range(1, 401):
    if n in (2, 4, 8):
        N = {2: 22, 4: 2112, 8: 21100112}[n]
    elif n % 10:
        N = pal_exists(n, n)
    else:
        s, nn = 0, n
        while nn % 10 == 0: nn //= 10; s += 1
        N = 10 ** s * pal_exists(nn, n - s)
    assert len(str(N)) == n and N % n == 0 and adm(N, n), n
print("(2) construction verified for n <= 400")
