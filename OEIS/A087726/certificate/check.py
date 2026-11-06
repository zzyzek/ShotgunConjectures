# OEIS A087726: number of X in M_2(Z/n) with X^2 = 0.
# 1. Brute force (all a,b,c,d mod n) for n <= 30 against the b-file.
# 2. Conjecture a(n) = n^2 <=> n squarefree on the b-file, n <= 1000.
# 3. For prime powers p^k <= 1000 with k >= 2: the three-family count of the
#    Lean proof, p^k phi + p^(k-1) phi + p^(3 floor(k/2) + ceil(k/2)), lies
#    strictly between p^(2k) and a(p^k).
# 4. R. Israel's prime-power formula (proved in the Lean file) against the b-file,
#    and the recursion a(p^(m+2)) = p^(2m+2)(p^2-1) + p^4 a(p^m).
import sys

def brute(n):
    c = 0
    for a in range(n):
        for b in range(n):
            for cc in range(n):
                if (a * a + b * cc) % n:
                    continue
                for d in range(n):
                    if (a * b + b * d) % n == 0 and (cc * a + d * cc) % n == 0 and (cc * b + d * d) % n == 0:
                        c += 1
    return c

def factor(n):
    f, p = {}, 2
    while p * p <= n:
        while n % p == 0:
            f[p] = f.get(p, 0) + 1
            n //= p
        p += 1
    if n > 1:
        f[n] = f.get(n, 0) + 1
    return f

b = {}
for line in open(sys.argv[1]):
    if line.strip() and not line.startswith('#'):
        n, v = map(int, line.split())
        b[n] = v
for n in range(1, 31):
    assert brute(n) == b[n], n
for n, v in b.items():
    sqf = all(e == 1 for e in factor(n).values())
    assert (v == n * n) == sqf, n
    assert v >= n * n, n
for n, v in b.items():
    f = factor(n)
    if len(f) == 1:
        (p, k), = f.items()
        if k >= 2:
            phi = p ** (k - 1) * (p - 1)
            fam = p ** k * phi + p ** (k - 1) * phi + p ** (3 * (k // 2) + (k + 1) // 2)
            assert p ** (2 * k) < fam <= v, (n, fam, v)
        israel = (1 + 3 * p * p + 2 * k * (p * p - 1) + (-1) ** k * (p * p - 1)) * p ** (2 * k - 2) // 4
        assert israel == v, (n, israel, v)
        if k >= 2:
            assert v == p ** (2 * k - 2) * (p * p - 1) + p ** 4 * b[p ** (k - 2)], n
print("OK: brute n <= 30; conjecture and a(n) >= n^2 for n <= %d; family bound, Israel formula and recursion on prime powers" % max(b))
