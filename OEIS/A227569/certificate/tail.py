# Follow each surviving prefix (exact to N) beyond N: the majority side's further
# contribution is below 1/(Pmaj*N), negligible; the minority side must represent
# x = (2 - base) * Pmin as F(Y), Y a set of integers > N (strictly increasing Engel sum).
# Strict Engel step: y = ceil(1/x); representable iff 1/y <= x <= (1 + U(y+1))/y; x <- y*x - 1.
import sys
from fractions import Fraction as Fr
import mpmath as mp
N = int(sys.argv[1]); mp.mp.dps = int(sys.argv[2])
T = Fr(2)
live = [(1, Fr(1), 1, Fr(0), "A")]
for n in range(2, N+1):
  nxt = []
  for Pa, Sa, Pb, Sb, w in live:
    for side in "AB":
      if side == "A": Pa2, Sa2, Pb2, Sb2 = Pa*n, Sa + Fr(1, Pa*n), Pb, Sb
      else:           Pa2, Sa2, Pb2, Sb2 = Pa, Sa, Pb*n, Sb + Fr(1, Pb*n)
      base = Sa2 + Sb2
      lo = base + min(Fr(1, Pa2), Fr(1, Pb2)) / (n+1)
      hi = base + (Fr(1, Pa2) + Fr(1, Pb2)) / n
      if lo <= T <= hi: nxt.append((Pa2, Sa2, Pb2, Sb2, w + side))
  live = nxt
def U(m):
  # F({m, m+1, ...}) = sum_{k>=m} (m-1)!/k!
  s = mp.mpf(0); t = mp.mpf(1); k = m
  while True:
    t /= k; s += t; k += 1
    if t < mp.mpf(10)**(-mp.mp.dps-5): return s
seen = set()
for Pa, Sa, Pb, Sb, w in live:
  key = (Sa + Sb, min(Pa, Pb))
  if key in seen: continue
  seen.add(key)
  Pmin, Pmaj = min(Pa, Pb), max(Pa, Pb)
  q = (T - Sa - Sb) * Pmin; x = mp.mpf(q.numerator) / q.denominator
  err = mp.mpf(Pmin) / mp.mpf(Pmaj) / N
  digits = []; m = N + 1; status = "alive"
  for step in range(60):
    if x <= 0: status = "x<=0"; break
    y = int(mp.ceil(1 / x))
    if y < m: status = "dead: y=%d < m" % y; break
    upper = (1 + U(y+1)) / y
    if x > upper: status = "dead: gap at y=%d" % y; break
    digits.append(y)
    x = y * x - 1; err *= y; m = y + 1
    if err > mp.mpf(10)**(-20) * x: status = "precision exhausted"; break
  print(w[:12], "min-side", [i+1 for i,c in enumerate(w) if c == ('A' if Pa == Pmin else 'B')][:8], "next digits", [str(d) if d < 10**12 else "%.3e" % d for d in digits][:12], status, flush=True)
