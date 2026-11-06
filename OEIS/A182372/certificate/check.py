# Checks for the A182372 proof (README steps 1-4).
#  (a) brute force: nonempty sets with perimeter n, split by (blocks b, 0 in S),
#      against Y_m(n) (m = 2b - [0 in S]) and against Arndt's two-sort
#      partitions, n <= 16;
#  (b) the q-identity sum_l x^{l(l+c)} [b,l] (x^{c+l+1};x)_{b-l} = 1, b, c <= 12;
#  (c) sum_{m>=1} Y_m (+1 for the empty set) against the b-file, n <= 200.
import sys
from collections import Counter

def sets_by_shape(n):
  out = Counter()
  for mask in range(1, 1 << (n + 1)):
    S = [i for i in range(n + 1) if (mask >> i) & 1]; T = set(S)
    if sum(x for x in S if not ((x - 1 in T) and (x + 1 in T))) != n: continue
    b = sum(1 for x in S if x - 1 not in T)
    out[2 * b - (1 if 0 in T else 0)] += 1
  return out

def Y(m, n):
  # 0 <= y1 < y2 <= y3 < y4 ..., length m, sum n (strict after odd positions)
  def rec(i, lo, rem):
    if i == m: return 1 if rem == 0 else 0
    tot = 0; y = lo
    while y * (m - i) <= rem:
      tot += rec(i + 1, (y + 1) if (i % 2 == 0) else y, rem - y); y += 1
    return tot
  return rec(0, 0, n)

def arndt(n):
  def rec(rem, last):
    tot = 1 if rem == 0 else 0
    for p in range(1, rem + 1):
      for s in (0, 1):
        if last is not None and (((p, s) <= last) or (s == last[1])): continue
        tot += rec(rem - p, (p, s))
    return tot
  return rec(n, None)

bad = 0
for n in range(0, 17):
  sh = sets_by_shape(n)
  ys = {m: Y(m, n) for m in range(1, 2 * n + 3)}
  ys = {m: v for m, v in ys.items() if v}
  if dict(sh) != ys: bad += 1; print("shape split fails", n, dict(sh), ys)
  if sum(sh.values()) != arndt(n): bad += 1; print("arndt fails", n)
print("(a) n <= 16 done")

# polynomials as coefficient lists
def pmul(a, b):
  r = [0] * (len(a) + len(b) - 1)
  for i, u in enumerate(a):
    if u:
      for j, v in enumerate(b): r[i + j] += u * v
  return r
def padd(a, b):
  r = [0] * max(len(a), len(b))
  for i, u in enumerate(a): r[i] += u
  for i, u in enumerate(b): r[i] += u
  return r
def mono(e): return [0] * e + [1]
def gauss(b, l):
  if l < 0 or l > b: return [0]
  if l == 0 or l == b: return [1]
  return padd(gauss(b - 1, l - 1), pmul(mono(l), gauss(b - 1, l)))
def poch(a, k):
  r = [1]
  for j in range(k): r = pmul(r, padd([1], [0] * (a + j) + [-1]))
  return r
def trim(a):
  while len(a) > 1 and a[-1] == 0: a = a[:-1]
  return a
for b in range(0, 13):
  for c in range(0, 13):
    s = [0]
    for l in range(0, b + 1):
      s = padd(s, pmul(pmul(mono(l * (l + c)), gauss(b, l)), poch(c + l + 1, b - l)))
    if trim(s) != [1]: bad += 1; print("q-identity fails", b, c)
print("(b) done")

N = 201
tot = [0] * N; tot[0] = 1
for m in range(1, 40):
  q = (m * m) // 4
  if q >= N: break
  r = [0] * N; r[q] = 1
  for j in range(1, m + 1):
    for i in range(j, N): r[i] += r[i - j]
  tot = [u + v for u, v in zip(tot, r)]
bf = {}
for line in open("b182372.txt"):
  t = line.split()
  if len(t) == 2 and not line.startswith("#"): bf[int(t[0])] = int(t[1])
for n, v in bf.items():
  if n < N and tot[n] != v: bad += 1; print("b-file mismatch", n, tot[n], v)
print("(c) b-file terms", len(bf))
print("problems", bad)
sys.exit(1 if bad else 0)
