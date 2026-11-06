#!/usr/bin/env python3
#
# Numerical check for OEIS A212916 (k = 10) and A229068 (k = 12):
# standard Young tableaux with n cells and at most k rows.
#
# 1. Regev's constant (arXiv:1004.4476 Thm 3.5 = Regev 1981 Cor. 4.4,
#    d = alpha = 1) equals Kotesovec's constant, and both equal the
#    rational-times-power constants printed in the two entries.
# 2. Exact counts a(n) agree with the printed terms, and
#    a(n) / (Kotesovec asymptotic) tends to 1 (polynomial extrapolation
#    in 1/n of log of the ratio at n = 100, 150, ..., 400).
#
# Exact counts for even k = 2m use Gordon's / Gessel's Bessel
# determinant (I. Gessel, J. Combin. Theory A 53 (1990) 257-285):
# sum_n a(n) x^n / n! = det[I_{i-j}(2x) + I_{i+j-1}(2x)], i, j = 1..m.
# The script cross-checks it against the hook-length sum over shapes
# for n <= 24 and against the printed terms.
#
# Run: nice -n 19 timeout 300 python3 check.py   (about 65 s)
#

from math import comb, factorial
from functools import lru_cache
import mpmath as mp

mp.mp.dps = 50

NMAX = 400

# Printed terms (OEIS A212916, A229068, data section, n = 0..14).
#
PRINTED = {
  10: [1,1,2,4,10,26,76,232,764,2620,9496,35695,140140,568360,2389192],
  12: [1,1,2,4,10,26,76,232,764,2620,9496,35696,140152,568503,2390466],
}

# Constants printed in the %F lines:
#   k=10: a(n) ~ 42525/32 * 10^(n+45/2) / (Pi^(5/2) n^(45/2))
#   k=12: a(n) ~ 602791875/128 * 12^(n+33) / (Pi^3 n^33)
# written as C_k * k^n * n^(-k(k-1)/4).
#
FCONST = {
  10: mp.mpf(42525)/32  * mp.mpf(10)**mp.mpf(22.5) / mp.pi**mp.mpf(2.5),
  12: mp.mpf(602791875)/128 * mp.mpf(12)**33 / mp.pi**3,
}

def regev_const(k):
  # Thm 3.5 of arXiv:1004.4476 (d = alpha = 1, s = k):
  # S_k(n) ~ (sqrt k)^(k(k-1)/2) (1/k!) n^(-k(k-1)/4) k^n
  #          Gamma(3/2)^(-k) prod_{j=1..k} Gamma(1+j/2).
  #
  p = mp.mpf(1)
  for j in range(1, k+1):
    p *= mp.gamma(1 + mp.mpf(j)/2)
  return (mp.sqrt(k)**(k*(k-1)/mp.mpf(2))) / factorial(k) * mp.gamma(mp.mpf(3)/2)**(-k) * p

def kotesovec_const(k):
  # k^n Pi^(-k/2) (k/n)^(k(k-1)/4) prod Gamma(j/2), with k^n n^(-k(k-1)/4) removed.
  #
  p = mp.mpf(1)
  for j in range(1, k+1):
    p *= mp.gamma(mp.mpf(j)/2)
  return mp.pi**(-mp.mpf(k)/2) * mp.mpf(k)**(k*(k-1)/mp.mpf(4)) * p

# EGF arithmetic on integer sequences e_t = t! [x^t] f.
#
def emul(a, b, N):
  return [ sum(comb(n, j)*a[j]*b[n-j] for j in range(n+1)) for n in range(N+1) ]

def bessel_egf(r, N):
  # t! [x^t] I_r(2x) = C(t, (t-r)/2) when t >= |r| and t - r even.
  #
  r = abs(r)
  return [ (comb(t, (t-r)//2) if ( (t >= r) and ((t-r) % 2 == 0) ) else 0) for t in range(N+1) ]

def syt_even(k, N):
  m   = k // 2
  ent = [ [ [x+y for x, y in zip(bessel_egf(i-j, N), bessel_egf(i+j-1, N))]
            for j in range(1, m+1) ] for i in range(1, m+1) ]

  # Laplace expansion along rows, memoised on the remaining column set.
  #
  @lru_cache(maxsize=None)
  def minor(row, cols):
    if row == m: return tuple([1] + [0]*N)
    acc  = [0]*(N+1)
    sign = 1
    for c in cols:
      rest = tuple(x for x in cols if x != c)
      prod = emul(ent[row][c], list(minor(row+1, rest)), N)
      acc  = [ (u + v if (sign > 0) else u - v) for u, v in zip(acc, prod) ]
      sign = -sign
    return tuple(acc)
  return list(minor(0, tuple(range(m))))

def partitions(n, k, mx=None):
  if mx is None: mx = n
  if n == 0:
    yield ()
    return
  if k == 0: return
  for p in range(min(n, mx), 0, -1):
    for rest in partitions(n-p, k-1, p):
      yield (p,) + rest

def hook_count(lam):
  n    = sum(lam)
  conj = [ sum(1 for r in lam if r > c) for c in range(lam[0]) ] if lam else []
  h    = 1
  for i, r in enumerate(lam):
    for c in range(r):
      h *= (r - c - 1) + (conj[c] - i - 1) + 1
  return factorial(n) // h

def syt_hook(k, n):
  return sum(hook_count(l) for l in partitions(n, k))

ok = True
for k in (10, 12):
  rc, kc = regev_const(k), kotesovec_const(k)
  print(f"k={k}: Regev const {mp.nstr(rc, 25)}")
  print(f"      Kotesovec   {mp.nstr(kc, 25)}")
  print(f"      %F line     {mp.nstr(FCONST[k], 25)}")
  ok &= (abs(rc/kc - 1) < mp.mpf(10)**-40) and (abs(FCONST[k]/kc - 1) < mp.mpf(10)**-40)

  a = syt_even(k, NMAX)
  for n in range(25):
    ok &= (a[n] == syt_hook(k, n))
  ok &= (a[:15] == PRINTED[k])
  print(f"      det formula = hook sum for n<=24, printed terms match: {ok}")

  # Ratio r(n) = a(n) / asymptotic.  It approaches 1 slowly, roughly
  # like (n/(n+b))^(k(k-1)/4), so extrapolate log r(n) (whose 1/n
  # expansion converges for n > b) by a polynomial in 1/n through
  # n = 100, 150, ..., 400.
  #
  ns = list(range(100, NMAX+1, 50))
  rs = [ mp.mpf(a[n]) / (kc * mp.mpf(k)**n * mp.mpf(n)**(-k*(k-1)/mp.mpf(4))) for n in ns ]
  M  = mp.matrix([[mp.mpf(1)/n**e for e in range(len(ns))] for n in ns])
  sol = mp.lu_solve(M, mp.matrix([mp.log(r) for r in rs]))
  print("      ratios at n=100,200,300,400:", [mp.nstr(rs[i], 8) for i in (0, 2, 4, 6)])
  print(f"      extrapolated limit of the ratio: {mp.nstr(mp.exp(sol[0]), 12)}")
  good = (abs(mp.exp(sol[0]) - 1) < mp.mpf(10)**-6)
  print(f"      limit within 1e-6 of 1: {good}")
  ok &= good

print("ALL OK" if ok else "FAILED")
