# Recompute A138683 (greedy, first term 2, sums avoid A001333) and A138684,
# compare with the OEIS data, test Layman's conjecture and the corrected form.
import sys
N = int(sys.argv[1]) if len(sys.argv) > 1 else 300000
Q = [1, 1]
while Q[-1] < 3 * N: Q.append(2 * Q[-1] + Q[-2])
Q = sorted(set(Q))
S = set(); s = []
for c in range(2, N + 1):
  if all((p - c) not in S for p in Q if p > c):
    S.add(c); s.append(c)
a = [None] + [s[i] - s[i - 1] for i in range(1, len(s))]   # a[n], n >= 1
data = [1,3,1,1,4,1,3,1,1,1,1,6,1,3,1,1,4,1,3,1,1,1,1,1,1,1,1,1,11,1,3,1,1,4,
  1,3,1,1,1,1,6,1,3,1,1,4,1,3,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,
  1,23,1,3,1,1,4,1,3,1,1,1,1,6,1,3,1,1,4,1,3,1,1,1,1,1,1,1,1,1,11,1,3,1,1,4,1]
assert a[1:len(data) + 1] == data, "data mismatch"
x = [None, 1, 2]; y = [None, 1, 3]; H = [1, 1]
while len(x) < 40: x.append(2 * x[-1] + x[-2]); y.append(y[-1] + y[-2])
while len(H) < 40: H.append(2 * H[-1] + H[-2])
z = [None, 1] + [(H[k - 1] + 5) // 2 for k in range(2, 40)]
M = len(a) - 1
def shape(v):
  bad = []
  for k in range(1, 39):
    if x[k + 1] > M: break
    if a[x[k]] != v[k]: bad.append((x[k], a[x[k]], v[k]))
    for n in range(x[k] + 1, 2 * x[k]):
      if a[n] != a[n - x[k]]: bad.append(n)
    for n in range(2 * x[k], x[k + 1]):
      if a[n] != 1: bad.append(n)
  return bad
print("terms", len(s), "a(n) known for n <=", M)
print("Layman (y) failures:", shape(y)[:10])
print("corrected (z) failures:", shape(z)[:10])
print("a(x(k)):", [a[x[k]] for k in range(1, 40) if x[k] <= M])
