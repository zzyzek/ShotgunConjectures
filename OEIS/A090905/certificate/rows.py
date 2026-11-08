# Compute rows of the A090905 triangle directly from the definition:
# row n = (e_{n-1}, e_n], e_n least with prod(row n-1) | prod(row n).
# Prints n, first, last, length, largest prime of row n-1, and e_n == 2*that prime.
import sys
LIM = int(sys.argv[1])
spf = list(range(LIM+1))
for i in range(2, int(LIM**0.5)+1):
  if spf[i] == i:
    for j in range(i*i, LIM+1, i):
      if spf[j] == j: spf[j] = i
def fac(m):
  d = {}
  while m > 1:
    p = spf[m]; d[p] = d.get(p,0)+1; m //= p
  return d
rows = [(1,1),(2,2)]
prev = {2:1}
e = 2; n = 2
print(1,1,1,1,None,None); print(2,2,2,1,None,None, flush=True)
while True:
  need = prev; have = {}
  unmet = len(need)
  E = e
  while unmet > 0:
    E += 1
    if E > LIM: sys.exit(0)
    for p,v in fac(E).items():
      old = have.get(p,0); have[p] = old+v
      if p in need and old < need[p] <= old+v: unmet -= 1
  n += 1
  ps = [m for m in range(rows[-1][0], rows[-1][1]+1) if m > 1 and spf[m] == m]
  lp = max(ps) if ps else None
  print(n, e+1, E, E-e, lp, lp is not None and E == 2*lp, flush=True)
  rows.append((e+1,E)); prev = have; e = E
