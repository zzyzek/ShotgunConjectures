# A214305 conjecture 2, strict reading: p2 fails for EVERY smaller two-factor
# Poulet p1 whose largest prime factor is d (d | p2).
#
import sys
twofac = []
out = []
with open(sys.argv[1]) as f:
  for line in f:
    t = line.split()
    if t and t[0] == 'C': t = t[1:]
    if not t or not t[0].isdigit(): continue
    n = int(t[0]); ps = [int(x) for x in t[1:]]
    if n > 200000: break
    for d in set(ps):
      cands = [p1 for p1, f1 in twofac if max(f1) == d]
      if cands and all((n - d) % (p1 - d) for p1 in cands):
        out.append((n, ps, d, cands))
    if len(ps) == 2 and ps[0] != ps[1]: twofac.append((n, ps))
print(len(out)); print(out[:6])
