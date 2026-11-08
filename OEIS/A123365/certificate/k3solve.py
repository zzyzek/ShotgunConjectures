# Complete search for omega(n) = 3, case A of A123365: n = p q^a r^b, p prime = 1 mod 6,
# q < r primes = 2 mod 3, equation (p + 2) c(q^a) c(r^b) = p q^a r^b + 2.
# For each p the search is complete by the bounds proved in docs/LADDER-perfect-2026-11-08.md (section K3):
#   q range, X = q^a <= Xmax(p, q), and r pinned to the window |kappa r^2 - p(r + 1) X| <= W.
# Mode "int" drops primality/mod-3 conditions (validation: must find (u, v, p) = (2, 8, 4) with a = b = 2).
import sys
from math import isqrt
from fractions import Fraction
from sympy import isprime, primerange

def s1(q, e):
  return sum(q**(j - 1) for j in range(1, e + 1) if (j - e) % 3 == 0)
def c(q, e):
  return 1 + (q - 1)*s1(q, e)

def root_hi(k, P, t):
  # an integer >= the positive root of k r^2 - P r - (P + t) = 0 (t may be negative)
  disc = P*P + 4*k*(P + t)
  if disc < 0: return None
  return (P + isqrt(disc) + 1)//(2*k) + 1
def root_lo(k, P, t):
  disc = P*P + 4*k*(P + t)
  if disc < 0: return 0
  return max(0, (P + isqrt(disc))//(2*k) - 1)

def solve_p(p, mode, qmax_override=None, stats=None):
  sols = []
  tgt = Fraction(p, p + 2)
  if mode == "prime":
    qs = [q for q in primerange(2, 3*p + 10) if q % 3 == 2]
  else:
    qs = list(range(2, qmax_override))
  for q in qs:
    Mq = q*q + q + 1
    if mode == "prime":
      # exponents allowed for q: q = 2: a = 1 mod 3; odd q: a >= 2, a != 1 mod 3
      aok = (lambda a: a % 3 == 1) if q == 2 else (lambda a: a >= 2 and a % 3 != 1)
      rmax = 1 if q == 2 else Fraction(c(q, 2), q*q)
      if not (rmax > tgt): continue
      Lq = Fraction(q*q, Mq)
      if not (Lq*Lq < tgt + Fraction(2, (p + 2)*q*(q + 1)**2)): continue
    else:
      aok = lambda a: a >= 2
    lam = 2*q*q - p*(q + 1)
    if lam < 0:
      Xmax = (p + 2)*(q*q + q)//(-lam) + 1
    else:
      R = p*Mq + 3
      Xmax = 3*(p + 2)**2*(q*q + q)*q*q*(R*R + 1)
    a = 1; X = q
    while X <= Xmax:
      if aok(a):
        cX = c(q, a); kap = (p + 2)*cX - p*X
        if kap > 0:
          Wb = (p + 2)*cX + -(-(p + 2)*cX//((q + 1)**2)) + 3
          P = p*X
          lo = max(q + 1, root_lo(kap, P, -Wb)); hi = root_hi(kap, P, Wb)
          if stats is not None: stats[0] += 1; stats[1] = max(stats[1], hi - lo + 1)
          for r in range(lo, hi + 1):
            G = kap*r*r - p*(r + 1)*X
            if abs(G) > Wb or G == 0: continue
            if mode == "prime" and not (r % 3 == 2 and isprime(r)): continue
            Mr = r*r + r + 1
            for e0, beta in ((2, r*r + 1), (0, r + 1), (1, r*r + r)):
              if mode == "prime" and e0 == 1: continue
              num = 2*Mr - (p + 2)*beta*cX
              if num % G: continue
              Y = num//G
              if Y < r*r: continue
              b = 0; Z = Y
              while Z % r == 0: Z //= r; b += 1
              if Z != 1 or b % 3 != e0: continue
              if (p + 2)*cX*c(r, b) == p*X*Y + 2:
                sols.append((p, q, a, r, b))
      a += 1; X *= q
  return sols

if __name__ == "__main__":
  mode = sys.argv[1]
  if mode == "int":
    st = [0, 0]
    print("int p=4:", solve_p(4, "int", 40, st), st)
  else:
    P0 = int(sys.argv[2]); st = [0, 0]; allsol = []; np_ = 0
    for p in primerange(7, P0 + 1):
      if p % 6 != 1: continue
      np_ += 1
      allsol += solve_p(p, "prime", stats=st)
    print("primes p = 1 mod 6 up to", P0, ":", np_, "X values tried", st[0], "max window", st[1], "solutions", allsol)
