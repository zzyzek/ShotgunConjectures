"""Sample two-sided coverings on a fixed prime set with CaDiCaL (random variable relabelling
and seeds), dedupe by orbit, and keep the least odd x over each orbit x -> +-2^t x.
Usage: python3 satcov.py L iters seed p1,p2,... [require_all]"""
import sys, random, subprocess, os, json, math
from sympy import n_order
from sympy.ntheory.modular import crt
L = int(sys.argv[1]); iters = int(sys.argv[2]); rng = random.Random(int(sys.argv[3]))
S = [int(t) for t in sys.argv[4].split(',')]
require_all = len(sys.argv) > 5 and sys.argv[5] == "1"
opts = []
for p in S:
  m = int(n_order(2, p))
  for c in range(m):
    r = pow(2, c, p)
    if m % 2 == 0:
      cov = [(-1, b) for b in range(c, L, m)] + [(1, b) for b in range((c + m // 2) % m, L, m)]
      opts.append((p, r, cov))
    else:
      opts.append((p, r, [(-1, b) for b in range(c, L, m)]))
      opts.append((p, (-r) % p, [(1, b) for b in range(c, L, m)]))
byp = {}
for i, o in enumerate(opts): byp.setdefault(o[0], []).append(i)
tgt = {}
for i, o in enumerate(opts):
  for t in o[2]: tgt.setdefault(t, []).append(i)
assert len(tgt) == 2 * L
def orbit_min(assign):
  ps = [p for p, r in assign]; rs = [r for p, r in assign]
  best = None
  for t in range(L):
    for sg in (1, -1):
      res = [(sg * pow(2, t, p) * r) % p for p, r in zip(ps, rs)]
      x = int(crt(ps + [2], res + [1])[0])
      if best is None or x < best: best = x
  return best
def canon(assign):
  # orbit representative: lexicographically least residue vector over the orbit
  ps = [p for p, r in assign]; rs = [r for p, r in assign]
  return min(tuple(zip(ps, [(sg * pow(2, t, p) * r) % p for p, r in zip(ps, rs)])) for t in range(L) for sg in (1, -1))
cnf = "/tmp/claude-1000/-home-z-git-github/176d1bb0-f16b-4cb7-9a3a-e6ba8f5cb8e1/scratchpad/satcov_%d.cnf" % os.getpid()
seen = set(); best = None; blocks = []
for it in range(iters):
  perm = list(range(len(opts))); rng.shuffle(perm)
  v = {i: perm[i] + 1 for i in range(len(opts))}
  cls = []
  for t, lst in tgt.items(): cls.append([v[i] for i in lst])
  for p, lst in byp.items():
    for a in range(len(lst)):
      for b in range(a + 1, len(lst)): cls.append([-v[lst[a]], -v[lst[b]]])
    if require_all: cls.append([v[i] for i in lst])
  for bl in blocks: cls.append([-v[i] for i in bl])
  rng.shuffle(cls)
  with open(cnf, "w") as f:
    f.write("p cnf %d %d\n" % (len(opts), len(cls)))
    for c in cls: f.write(" ".join(map(str, c)) + " 0\n")
  out = subprocess.run(["cadical", "-q", "--seed=%d" % rng.randrange(10**9), "--phase=%d" % rng.randrange(2), cnf], capture_output=True, text=True, timeout=600).stdout
  if "UNSAT" in out:
    print("UNSAT after", it, flush=True); break
  lits = [int(t) for ln in out.splitlines() if ln.startswith("v") for t in ln.split()[1:]]
  inv = {perm[i] + 1: i for i in range(len(opts))}
  chosen = sorted(inv[l] for l in lits if l > 0)
  blocks.append(chosen)
  assign = sorted((opts[i][0], opts[i][1]) for i in chosen)
  key = canon(assign)
  if key in seen: continue
  seen.add(key)
  x = orbit_min(assign)
  if best is None or x < best:
    best = x
    print("iter", it, "orbits", len(seen), "x", x, "digits", len(str(x)), "assign", json.dumps(assign), flush=True)
print("orbits", len(seen), "best", best)
os.remove(cnf)
