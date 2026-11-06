# A005329 / A075271 / A075272: recompute A075271 from its BinomialMean
# recurrence, its BM transform, and the binomial transform of A005329;
# compare with the OEIS data (S lines fetched 2026-11-06) and check the
# key identity Sum_k C(n,k) b(k+1) = 2^(n+1) b(n).
#
from math import comb
N = 40
c = [1]
for i in range(1, N + 2):
  c.append(c[-1] * (2**i - 1))
b = [sum(comb(n, k) * c[k] for k in range(n + 1)) for n in range(N + 2)]
a = [1]
for n in range(1, N):
  s = sum(comb(n, k) * a[k] for k in range(n))
  a.append(2**(n + 1) * a[n - 1] - s)
bm = []
for n in range(N):
  t = sum(comb(n, k) * a[k] for k in range(n + 1))
  assert t % 2**n == 0
  bm.append(t // 2**n)
assert bm == b[:N]
assert all(2 * a[n] == b[n + 1] for n in range(N))
assert all(sum(comb(n, k) * b[k + 1] for k in range(n + 1)) == 2**(n + 1) * b[n] for n in range(N))
assert all(sum((-1)**(n - k) * comb(n, k) * bm[k] for k in range(n + 1)) == c[n] for n in range(N))
oeis71 = [1, 3, 17, 211, 5793, 339491, 41326513, 10282961907, 5181436229441]
oeis72 = [1, 2, 6, 34, 422, 11586, 678982, 82653026, 20565923814, 10362872458882]
assert a[:len(oeis71)] == oeis71 and bm[:len(oeis72)] == oeis72
print("OK n <", N)
