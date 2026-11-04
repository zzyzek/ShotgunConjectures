# Certify the [lo, N] threshold: a satisfying colouring of [lo, N-1] (saved
# and re-checked by brute force) and an UNSAT run on [lo, N] with a DRAT
# proof written by CaDiCaL.
#
import sys, time
from pysat.solvers import Cadical153
from pysat.formula import CNF
lo, N = int(sys.argv[1]), int(sys.argv[2])
def clauses(M):
  C = []
  for x in range(lo, M + 1):
    for y in range(x + 1, M // x + 1):
      p, q = x * y, x + y
      if len({x, y, q, p}) == 4:
        C.append([x, y, q, p]); C.append([-x, -y, -q, -p])
  return C
C1 = clauses(N - 1)
with Cadical153(bootstrap_with=C1) as s:
  assert s.solve()
  m = s.get_model()
col = {abs(v): int(v > 0) for v in m}
bad = [(x, y) for x in range(lo, N) for y in range(x + 1, (N - 1) // x + 1)
       if col.get(x, 0) == col.get(y, 0) == col.get(x + y, 0) == col.get(x * y, 0)]
print("colouring of [%d,%d] monochromatic tuples:" % (lo, N - 1), len(bad))
open("work/NT-E29.1/colouring_%d_%d.txt" % (lo, N - 1), "w").write(
  "".join(str(col.get(n, 0)) for n in range(lo, N)) + "\n")
C2 = clauses(N)
CNF(from_clauses=C2).to_file("work/NT-E29.1/unsat_%d_%d.cnf" % (lo, N))
t = time.time()
with Cadical153(bootstrap_with=C2, with_proof=True) as s:
  r = s.solve()
  pr = s.get_proof()
print("[%d,%d] solve:" % (lo, N), r, "time", round(time.time() - t, 1), "proof lines", len(pr))
open("work/NT-E29.1/unsat_%d_%d.drat" % (lo, N), "w").write("\n".join(pr) + "\n")
