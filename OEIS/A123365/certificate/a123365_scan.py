# Count n < N with 3*c(n) = n + 2 (c = number of cubes mod n), by number of
# distinct prime factors. c is multiplicative; c(p) has a closed form,
# prime powers p^e (e >= 2) are counted by brute force.
#
import sys
N = int(sys.argv[1])
spf = list(range(N))
for i in range(2, int(N ** 0.5) + 1):
  if spf[i] == i:
    for j in range(i * i, N, i):
      if spf[j] == j:
        spf[j] = i
cache = {}
def cpp(p, e):
  q = p ** e
  if e == 1:
    return ( (p - 1) // 3 + 1 if p % 3 == 1 else p )
  if q not in cache:
    cache[q] = len({ (x * x * x) % q for x in range(q) })
  return cache[q]
hits = {}
for n in range(1, N):
  m, c, w = n, 1, 0
  while m > 1:
    p, e = spf[m], 0
    while m % p == 0:
      m //= p
      e += 1
    c *= cpp(p, e)
    w += 1
  if 3 * c == n + 2:
    hits.setdefault(w, []).append(n)
for w in sorted(hits):
  print(w, len(hits[w]), hits[w][:5])
