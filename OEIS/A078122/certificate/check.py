# Build A078122 from its definition (lower triangular, M(k,0) = M(k,k) = 1,
# [M^3](i,j) = M(i+1,j+1)) row by row, for base m = 3 (and m = 2, 4 for the
# companion entries), and compare with N(n,k) = number of m-ary partitions of
# m^n with largest part m^(n-k), with the b-files, and the row sums with A078125.
import sys

def build(m, R):
  M = [[1]]
  for i in range(R - 1):
    # P = M^m restricted to rows <= i (only rows <= i of M are needed)
    P = [[1 if a == b else 0 for b in range(i + 1)] for a in range(i + 1)]
    for _ in range(m):
      P = [[sum(P[a][c] * M[c][b] for c in range(b, a + 1)) for b in range(i + 1)] for a in range(i + 1)]
    M.append([1] + [P[i][j] for j in range(i + 1)])
  return M

def mparts_maxpart(m, N, r):
  # m-ary partitions of N with all parts <= m^r
  f = [1] * (N + 1)
  for t in range(1, r + 1):
    p = m ** t
    for s in range(p, N + 1): f[s] += f[s - p]
  return f

def Nmat(m, R):
  T = []
  for n in range(R):
    row = []
    for k in range(n + 1):
      r = n - k
      if r == 0: row.append(1); continue
      # largest part exactly m^r: remove one part m^r, rest parts <= m^r
      row.append(mparts_maxpart(m, m ** n - m ** r, r)[m ** n - m ** r])
    T.append(row)
  return T

bad = 0
for m, R in ((2, 13), (3, 10), (4, 8)):
  M = build(m, R); T = Nmat(m, R)
  if M != T: bad += 1; print("mismatch base", m)
  else: print("base", m, "rows 0..%d: M = N" % (R - 1))

M = build(3, 10)
flat = [v for row in M for v in row]
bf = [int(l.split()[1]) for l in open("b078122.txt") if l.strip() and not l.startswith("#")]
if flat != bf[:len(flat)]: bad += 1; print("b078122 mismatch")
rs = [sum(r) for r in M]
b5 = [int(l.split()[1]) for l in open("b078125.txt") if l.strip() and not l.startswith("#")]
if rs != b5[:len(rs)]: bad += 1; print("row sums vs A078125 mismatch")
print("b-file entries compared", len(flat), "row sums", rs)
print("problems", bad)
sys.exit(1 if bad else 0)
