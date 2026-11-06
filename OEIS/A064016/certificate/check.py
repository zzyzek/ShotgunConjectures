# a(n) = Sum_{k<=10^n} (k - phi(k)) for n <= 6 against the OEIS data, and the
# ratios a(n)/10^(2n) vs 1/2 - 3/pi^2 and (1/n^2) Sum_{j<=n} a(j).
import math
data = [0, 23, 2006, 196308, 19607514, 1960399246, 196036947608]
N = 10 ** 6
phi = list(range(N + 1))
for p in range(2, N + 1):
  if phi[p] == p:
    for m in range(p, N + 1, p):
      phi[m] -= phi[m] // p
s = 0; vals = []; idx = 0
for k in range(1, N + 1):
  s += k - phi[k]
  if k == 10 ** idx:
    vals.append(s); idx += 1
assert vals == data, vals
c = 0.5 - 3 / math.pi ** 2
for n, v in enumerate(vals):
  print(n, v, v / 10 ** (2 * n), c, sum(vals[1:n + 1]) / max(n, 1) ** 2)
