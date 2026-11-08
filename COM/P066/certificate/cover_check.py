# COM-P066 part 1 (Coman C126 restated): build the residue class a mod M of P
# with P = 1 (mod 12), P = 1 (mod 5) and P = -5^r (mod q) for two disjoint
# coverings of the odd m by classes m = r (mod ord_q(5)); check the coverings
# exhaustively and spot-check (P + 5^m)/6^n for members P of the class.
from math import gcd, prod
cover1 = [(13, 4, 1), (313, 8, 3), (17, 16, 7), (11489, 16, 15)]
cover2 = [(31, 3, 0), (7, 6, 1), (601, 12, 5), (390001, 24, 11), (19, 9, 2), (829, 9, 5), (5167, 18, 17)]
def isprime(n):
    if n < 2: return False
    i = 2
    while i * i <= n:
        if n % i == 0: return False
        i += 1
    return True
for q, o, r in cover1 + cover2:
    assert isprime(q) and pow(5, o, q) == 1 and all(pow(5, d, q) != 1 for d in range(1, o)), q
for cov, L in ((cover1, 16), (cover2, 144)):
    for m in range(1, L, 2):
        assert any(m % o == r for q, o, r in cov), (L, m)
qs = [q for q, _, _ in cover1 + cover2]
assert len(set(qs)) == len(qs)
M = 4 * 3 * 5 * prod(qs)
# CRT
def crt(res):
    x, m = 0, 1
    for r, n in res:
        t = ((r - x) * pow(m, -1, n)) % n
        x += m * t; m *= n
    return x % m
a = crt([(1, 4), (1, 3), (1, 5)] + [((-pow(5, r, q)) % q, q) for q, o, r in cover1 + cover2])
print("M =", M); print("a =", a); print("gcd(a, M) =", gcd(a, M))
# spot-check: for P = a + jM, every m in 1..300, every n with 6^n | P+5^m
for j in range(3):
    P = a + j * M
    for m in range(1, 301):
        V0 = P + 5**m
        assert V0 % 4 == 2
        ns = [0] + ([1] if V0 % 3 == 0 else [])
        assert (V0 % 3 == 0) == (m % 2 == 1)
        for n in ns:
            V = V0 // 6**n
            if n == 0:
                assert V % 2 == 0 and (V // 2) % 2 == 1 and V // 2 > 1
            else:
                assert len([q for q in qs if V % q == 0]) >= 2, (j, m, n)
print("spot-check OK: P = a + jM (j < 3), m <= 300: n = 0: P+5^m = 2*odd>2; n = 1: two cover primes divide")
