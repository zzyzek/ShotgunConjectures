# A219033: checks (1) the family k = 434 m, x = 428 m, y = 6 m satisfies sigma_1 and sigma_2 equalities
# for all m <= 3000 coprime to 2*3*7*31*107 and fails for m = 107; (2) 107 is in A185208
# (no divisor d > 1 with d + 1 a prime power); (3) the sequence terms below 60400 (brute force over all
# x + y = k, k <= B) match the OEIS data; (4) parity / sigma_3 observations below B.
import sys
from math import gcd
L = 434*3000
B = 16100
s1 = [0]*(L+1); s2 = [0]*(L+1); s3 = [0]*(L+1)
for d in range(1, L+1):
  for m in range(d, L+1, d):
    s1[m] += d; s2[m] += d*d; s3[m] += d**3
def sig(e, n):
  return (s1, s2, s3)[e-1][n]
def ppow(n):
  if n < 2: return False
  p = next(q for q in range(2, n+1) if n % q == 0)
  while n % p == 0: n //= p
  return n == 1
bad = 0
for m in range(1, 3001):
  ok = all(sig(e, 434*m) == sig(e, 428*m) + sig(e, 6*m) for e in (1, 2))
  cop = gcd(m, 2*3*7*31*107) == 1
  if cop and not ok: bad += 1; print("family fails", m)
fam107 = [sig(e, 434*107) - sig(e, 428*107) - sig(e, 6*107) for e in (1, 2)]
print("m=107 differences sigma_1, sigma_2:", fam107)
if fam107[0] == 0: bad += 1
in185208 = all(not ppow(d+1) for d in range(2, 108) if 107 % d == 0)
print("107 in A185208:", in185208)
if not in185208: bad += 1
DATA = [434,2170,4774,5642,7378,8246,9982,10850,12586,16058,17794,18662,20398,23002,23870,25606,26474,
        28210,29078,30814,31682,34286,36022,36890,38626,41230,42098,43834,44702,47306,49042,49910,52514,
        54250,55118,56854,59458,60326]
seq = []; odd_parts = 0; s3hits = 0
for k in range(2, B+1):
  hit = False
  for x in range(1, k//2+1):
    y = k - x
    if s1[x] + s1[y] == s1[k] and s2[x] + s2[y] == s2[k]:
      hit = True
      if x % 2 or y % 2: odd_parts += 1
      if s3[x] + s3[y] == s3[k]: s3hits += 1
  if hit: seq.append(k)
print("terms <= %d:" % B, len(seq), "match data:", seq == [k for k in DATA if k <= B], "odd terms:", sum(k % 2 for k in seq),
      "partitions with an odd part:", odd_parts, "sigma_3 hits:", s3hits)
if seq != [k for k in DATA if k <= B]: bad += 1
print("failures:", bad); sys.exit(1 if bad else 0)
