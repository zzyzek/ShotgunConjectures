# A084029: numerical check of the counting construction for n in [131, NMAX].
# Case (i)  n = p^k, gcd(n,10) = 1, ord_n(10) > (n-1)/2: triple 2*10^0 + 10^t (10^t == -2) plus
#           (n-3)/2 pairs 10^i + 10^(i+h) (10^h == -1), slot n-1-h always used; count C((n-1)/2, 2).
# Case (ii) otherwise: a base solution N0 with digits <= 2 (found here by a DP, standing in for EGZ),
#           then single-unit moves i -> i -+ r inside [e, n-1) on an injective source set A with
#           2^|A| >= n. We build 2^min(|A|,12) variants and check each one.
import sys
from math import comb
def ordmod(a, m):
    if m == 1:
        return 1
    x, k = a % m, 1
    while x != 1:
        x = x * a % m; k += 1
    return k
def split(n):
    a = b = 0; m = n
    while m % 2 == 0: m //= 2; a += 1
    while m % 5 == 0: m //= 5; b += 1
    return a, b, m
def ok(digs, n):
    N = sum(d * 10 ** i for i, d in enumerate(digs))
    return (all(0 <= d <= 9 for d in digs) and digs[n - 1] >= 1 and sum(digs) == n and N % n == 0)
def base_solution(n):
    # DP for a digit vector with digits <= 2, top >= 1, sum n, value == 0 mod n (exists by EGZ + shift).
    from functools import lru_cache
    import sys
    sys.setrecursionlimit(10000)
    # forward DP over positions 0..n-1 storing reachable (sum, residue) with back-pointers
    reach = [dict() for _ in range(n + 1)]
    reach[0][(0, 0)] = None
    for i in range(n):
        p = pow(10, i, n)
        for (s, res) in reach[i]:
            for d in (0, 1, 2):
                if i == n - 1 and d == 0:
                    continue
                key = (s + d, (res + d * p) % n)
                if key[0] <= n and key not in reach[i + 1]:
                    reach[i + 1][key] = (s, res, d)
    key = (n, 0)
    assert key in reach[n]
    digs = [0] * n
    for i in range(n, 0, -1):
        s, res, d = reach[i][key]
        digs[i - 1] = d; key = (s, res)
    return digs
NMAX = int(sys.argv[1])
for n in range(131, NMAX + 1):
    a, b, m = split(n)
    e = a + b
    r = ordmod(10, m)
    if a + b == 0 and 2 * r > n - 1:
        h = r // 2
        assert pow(10, h, n) == n - 1
        t = next(t for t in range(r) if pow(10, t, n) == (n - 2) % n)
        slots = list(range(0, n - h))
        top = n - 1 - h
        others = [s for s in slots if s != top]
        need = (n - 3) // 2 - 1
        assert len(others) >= need and comb(len(others), need) >= n
        for shift in range(5):
            S = others[shift:shift + need] if shift + need <= len(others) else others[:need]
            digs = [0] * n
            digs[0] += 2; digs[t] += 1
            for s in S + [top]:
                digs[s] += 1; digs[s + h] += 1
            assert ok(digs, n), n
        print(n, "case i, count >=", comb(len(others), need))
        continue
    assert 2 * r <= n - 1 - e, n
    N0 = base_solution(n)
    assert ok(N0, n)
    blk = lambda i: (i - e) // r
    nz = [i for i in range(e, n - 1) if N0[i] > 0]
    odd = [(i, i - r) for i in nz if blk(i) % 2 == 1]
    even = []
    used = set()
    for i in nz:
        if blk(i) % 2 == 0:
            j = i + r if blk(i) == 0 else i - r
            if j not in used:
                used.add(j); even.append((i, j))
    A = odd if len(odd) >= len(even) else even
    assert 2 ** len(A) >= n, (n, len(A))
    k = min(len(A), 12)
    for mask in range(2 ** k):
        digs = N0[:]
        for bit in range(k):
            if mask >> bit & 1:
                i, j = A[bit]; digs[i] -= 1; digs[j] += 1
        assert ok(digs, n), (n, mask)
    print(n, "case ii, |A| =", len(A))
