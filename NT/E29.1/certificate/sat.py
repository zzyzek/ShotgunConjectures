# Least N such that every 2-colouring of [lo,N] has distinct x,y,x+y,xy
# all one colour. Incremental: add clauses as N grows, solve with assumptions none.
import sys, time
from pysat.solvers import Cadical153
lo = int(sys.argv[1]); Nmax = int(sys.argv[2]); step = int(sys.argv[3]) if len(sys.argv) > 3 else 1
s = Cadical153()
t0 = time.time()
N = lo
def add_upto(M, prev):
  for x in range(lo, M + 1):
    for y in range(x + 1, M // x + 1):
      p = x * y
      if (p <= prev) or (p > M):
        continue
      q = x + y
      if len({x, y, q, p}) < 4:
        continue
      s.add_clause([x, y, q, p]); s.add_clause([-x, -y, -q, -p])
prev = lo
for N in range(lo + step, Nmax + 1, step):
  add_upto(N, prev); prev = N
  if not s.solve():
    print("UNSAT at N <=", N, "time", round(time.time() - t0, 1), flush=True)
    break
else:
  print("SAT up to", Nmax, "time", round(time.time() - t0, 1))
