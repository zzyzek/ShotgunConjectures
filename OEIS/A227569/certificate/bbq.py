# Exact branch and bound (Fractions) for F(A) + F(B) = T over partitions of {1,2,...}, 1 in A.
# Completion of a prefix (decisions for 1..n) lies in [base + min(1/Pa,1/Pb)/(n+1), base + (1/Pa+1/Pb)/n],
# using F(X) <= F({m,m+1,...}) <= 1/(m-1) for X inside {m, m+1, ...} (F is monotone under inclusion).
import sys
from fractions import Fraction as Fr
T = Fr(sys.argv[1]); N = int(sys.argv[2])
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
  if n % 5 == 0 or len(live) < 3: print(n, len(live), flush=True)
  if not live or len(live) > 200000: break
for x in live[:20]: print(x[4], float(x[1] + x[3]))
