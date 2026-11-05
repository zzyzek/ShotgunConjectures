# Second reading of the constants in B2_1_mathlib.lean and of the bounds
# for every n up to a limit (default 6000).
#
from fractions import Fraction as F
import sys

LIMIT = int(sys.argv[1]) if len(sys.argv) > 1 else 6000

# Head of the harmonic sum over d >= 5 coprime to 6, d < 200 (Lean: B2_h6_head).
#
C = sum(F(1, d) for d in range(5, 200) if d % 6 in (1, 5))
assert C <= F(11, 8)
print("sum_{5<=d<200, (d,6)=1} 1/d =", float(C), "<= 11/8")

# Odd squares: sum_{odd d >= 5} 1/d^2 <= 1/8 (telescoping), so with d = 3
# the odd sum is <= 17/72 (Lean: B2_v5_sum).
#
S5 = sum(F(1, d * d) for d in range(5, 4001, 2))
assert S5 <= F(1, 8)
print("sum_{odd 5<=d<=4001} 1/d^2 =", float(S5), "<= 1/8")

# Odd-n threshold: K <= K/2 + 11/2 + N/50 with N = n+1 <= 12K+23 forces K <= 22,
# while n >= 300 gives K = (n-2r)/12 >= 24.
#
for K in range(0, 100):
  if F(K) <= F(K, 2) + F(11, 2) + F(12 * K + 23, 50):
    kmax = K
print("largest K not excluded:", kmax)
assert kmax <= 22 and (300 - 10) // 12 >= 23

# sigma table, deficiency, and the actual Markov sums for every n <= LIMIT.
#
s = [0] * (LIMIT + 2)
for d in range(1, LIMIT + 2):
  for m in range(d, LIMIT + 2, d):
    s[m] += d
defi = [m > 0 and s[m] < 2 * m for m in range(LIMIT + 2)]
for n in range(2, LIMIT + 1):
  assert any(defi[a] and defi[n - a] for a in range(1, n)), n
print("every 2 <= n <=", LIMIT, "is a sum of two deficient numbers")

# rs(t) = sigma(t)/t - 1.  Check the bound actually used in the odd case,
# 3*sum rs(m_k) + sum rs(c-12k) < K, for odd n in [300, LIMIT].
#
def rs(t):
  return F(s[t], t) - 1

worst = 0
for n in range(301, LIMIT + 1, 2):
  r = 5 if n % 3 == 2 else 1
  c = n - 2 * r
  K = c // 12
  tot = sum(3 * rs(6 * k + r) + rs(c - 12 * k) for k in range(K))
  worst = max(worst, tot / K)
  assert tot < K, n
print("odd n in [301, %d]: max (3 sum rs(m) + sum rs(b)) / K = %.4f" % (LIMIT, worst))
