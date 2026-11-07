# Checks for A219431: overpartition count = sum over partitions of 2^(distinct parts),
# a(n) from G * A = x G' matches OEIS data, and the mod 4 pattern for n <= 60.
import sys
N = 60
M = N * N
# overpartitions via prod (1+x^k)/(1-x^k)
c = [0] * (M + 1); c[0] = 1
for k in range(1, M + 1):
    for i in range(M, k - 1, -1):
        c[i] += c[i - k]          # times (1 + x^k)
    for i in range(k, M + 1):
        c[i] += c[i - k]          # times 1/(1 - x^k)
def parts(n, mx):
    if n == 0:
        yield []
        return
    for p in range(min(n, mx), 0, -1):
        for rest in parts(n - p, p):
            yield [p] + rest
for m in range(0, 26):
    assert c[m] == sum(2 ** len(set(l)) for l in parts(m, m)), m
b = [c[n * n] for n in range(N + 1)]
a = [0] * (N + 1)
for n in range(1, N + 1):
    a[n] = n * b[n] - sum(a[k] * b[n - k] for k in range(1, n))
assert a[1:10] == [2, 24, 386, 6832, 128442, 2505720, 50153770, 1022997344, 21170657906]
for n in range(1, N + 1):
    assert b[n] % 4 == 2
    assert a[n] % 4 == (2 if n % 2 else 0)
print("ok: definition, OEIS data a(1..9), mod 4 pattern n <= %d" % N)
