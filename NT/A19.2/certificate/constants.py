# Numeric companion to A19_2_mathlib.lean (the Lean file proves all of
# this symbolically; this script is a second reading of the constants).
#
# Parameters for s >= 20: y = 2310 s, L = 4851 s, K = 2L, x = 2^K,
# R = product of odd primes <= y, M = 4R <= 2^(2y+2).
#
from fractions import Fraction as F
from math import gcd, log

# phi(2310) by direct count.
#
phi = sum(1 for r in range(2310) if gcd(r, 2310) == 1)
print("phi(2310) =", phi)

# K * sigma <= 23/25 with sigma = 480 / (2310^2 (s - 1)), K = 9702 s.
# The left side decreases in s, so s = 20 is the worst case.
#
for s in (20, 21, 100, 10**6):
  ks = F(9702 * s * 480, 2310**2 * (s - 1))
  print("s = %7d  K*sigma = %.6f  <= 23/25: %s" % (s, float(ks), ks <= F(23, 25)))

# Final inequality 25 (2 L 2^L + 2) < 2 * 2^(5082 s - 2), in log2 form for s = 20
# (the Lean lemma A19_final proves it for all s >= 20).
#
s   = 20
L   = 4851 * s
lhs = log(25 * (2 * L + 2), 2) + L
rhs = 1 + (5082 * s - 2)
print("s = 20: log2 lhs = %.1f, log2 rhs = %d" % (lhs, rhs))

# Block bound check: for y = 2310 s, sum over m in (y, B] coprime to 2310 of 1/m^2
# against 480 / (2310^2 (s - 1)), and the true prime sum over (y, B].
#
def primes_upto(N):
  f = bytearray([1]) * (N + 1)
  f[0] = f[1] = 0
  for i in range(2, int(N**0.5) + 1):
    if f[i]:
      f[i*i::i] = bytearray(len(f[i*i::i]))
  return f

B  = 3 * 10**6
pf = primes_upto(B)
for s in (2, 5, 20, 100):
  y  = 2310 * s
  if y >= B:
    continue
  cs = sum(1.0 / (m * m) for m in range(y + 1, B + 1) if gcd(m, 2310) == 1)
  ps = sum(1.0 / (p * p) for p in range(y + 1, B + 1) if pf[p])
  bd = 480 / (2310**2 * (s - 1))
  print("s = %3d  coprime sum = %.3e  prime sum = %.3e  bound = %.3e" % (s, cs, ps, bd))

# The original sketch in the scan note (z = C log x / log log x, K = log2 x):
# K * sum_{p > z} 1/p^2 at a few x, by direct prime sums, to show the union
# bound is genuinely small only with the prime sum, not a crude one.
#
for lx in (50, 200, 1000):
  K  = lx / log(2)
  z  = int(3 * lx / log(lx))
  ps = sum(1.0 / (p * p) for p in range(z + 1, B + 1) if pf[p])
  print("ln x = %4d  z = %4d  K * sum_{p>z} 1/p^2 = %.3f" % (lx, z, K * ps))
