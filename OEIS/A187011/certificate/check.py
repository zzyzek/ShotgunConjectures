# A187011 check: exact det(|p_i - p_j|) by fraction-free (Bareiss)
# elimination against the closed form
#   (-1)^(n-1) 2^(n-2) (p_n - 2) prod_{i<n} (p_{i+1} - p_i)
# proved in A187011_mathlib.lean, against the data terms of the entry,
# and the closed form for random strictly increasing integer sequences.
# Also prints (1/n) sum log(gap) and log|a(n)|/n to show the slow growth.
#
# Usage: python3 check.py
#
import math, random

NDET = 60
NLOG = 10 ** 6

# Primes by a plain sieve.
#
def primes_upto(N):
  s = bytearray([1]) * (N + 1)
  s[0] = s[1] = 0
  for q in range(2, math.isqrt(N) + 1):
    if s[q]:
      s[q * q::q] = bytearray(len(s[q * q::q]))
  return [i for i in range(N + 1) if s[i]]

# Bareiss elimination with row swaps, exact over the integers.
#
def det(M):
  M    = [row[:] for row in M]
  n    = len(M)
  sign = 1
  prev = 1
  for k in range(n - 1):
    if M[k][k] == 0:
      r = next((r for r in range(k + 1, n) if M[r][k] != 0), None)
      if r is None:
        return 0
      M[k], M[r] = M[r], M[k]
      sign = -sign
    for i in range(k + 1, n):
      for j in range(k + 1, n):
        M[i][j] = (M[i][j] * M[k][k] - M[i][k] * M[k][j]) // prev
    prev = M[k][k]
  return sign * M[n - 1][n - 1]

def closed(x):
  n = len(x)
  return ( (-1) ** (n - 1) * 2 ** (n - 2) * (x[-1] - x[0]) *
           math.prod(x[i + 1] - x[i] for i in range(n - 1)) )

def dist_det(x):
  return det([[abs(u - v) for v in x] for u in x])

P = primes_upto(16 * NLOG)

data = [1, 0, -1, 12, -80, 1152, -5632, 61440, -278528, 2752512, -42467328, 182452224,
        -2642411520, 23555211264, -99052683264, 869730877440, -11828339933184,
        158638912045056, -656820758642688, 8683393080360960, -73742045851680768,
        303517985824309248, -3950008716924813312]

ok_data = all(((n < 2) and (dist_det(P[:n]) == data[n])) or
              ((n >= 2) and (closed(P[:n]) == data[n]) and (dist_det(P[:n]) == data[n]))
              for n in range(1, len(data)))
print("data a(1..22) = det = closed form:", ok_data)

ok_p = all(dist_det(P[:n]) == closed(P[:n]) for n in range(2, NDET + 1))
print("det = closed form for primes, n = 2 ..", NDET, ":", ok_p)

random.seed(1)
ok_r = True
for t in range(200):
  n  = random.randint(2, 12)
  x  = sorted(random.sample(range(-1000, 1000), n))
  ok_r = ok_r and (dist_det(x) == closed(x))
print("det = closed form for 200 random increasing integer sequences:", ok_r)

# The sign of the closed form only needs every gap to be positive.
#
ok_s = all(P[i] < P[i + 1] for i in range(NLOG))
print("gaps positive for the first", NLOG, "primes:", ok_s)

# Growth: log|a(n)|/n = ((n-2) log 2 + log(p_n - 2) + sum log gaps) / n.
#
s = 0.0
for i in range(NLOG - 1):
  s += math.log(P[i + 1] - P[i])
  n = i + 2
  if n in (10, 100, 1000, 10 ** 4, 10 ** 5, 10 ** 6):
    la = (n - 2) * math.log(2) + math.log(P[n - 1] - 2) + s
    print("n =", n, " mean log gap =", round(s / (n - 1), 4), " log|a(n)|/n =", round(la / n, 4))
