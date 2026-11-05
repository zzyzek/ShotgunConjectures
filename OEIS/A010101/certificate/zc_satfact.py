# Independent check of a window fact "every length-m Z-channel code has at
# most b words of weight lo..hi": the CNF "b+1 such words, no conflict" is
# UNSAT. Writes the CNF and CaDiCaL's DRAT proof for rupcheck.
#
import sys, time
from pysat.card import CardEnc, EncType
from pysat.formula import CNF
from pysat.solvers import Solver

m, lo, hi, b = (int(x) for x in sys.argv[1:5])
V = [x for x in range(1 << m) if lo <= bin(x).count('1') <= hi]
var = {x: i + 1 for i, x in enumerate(V)}
cnf = CNF()
for x in V:
  for y in V:
    if x < y:
      p, q = bin(x & ~y).count('1'), bin(y & ~x).count('1')
      if max(p, q) <= 1:
        cnf.append([-var[x], -var[y]])
card = CardEnc.atleast(lits=list(var.values()), bound=b + 1, top_id=len(V), encoding=EncType.seqcounter)
cnf.extend(card.clauses)
tag = 'runs/fact_m%d_%d_%d_le%d' % (m, lo, hi, b)
cnf.to_file(tag + '.cnf')
t = time.time()
with Solver(name='cadical153', bootstrap_with=cnf.clauses, with_proof=True) as s:
  r = s.solve()
  print('m=%d weights %d..%d, >= %d words: %s (%.1fs, %d vars, %d clauses)' % (m, lo, hi, b + 1, 'SAT' if r else 'UNSAT', time.time() - t, cnf.nv, len(cnf.clauses)), flush=True)
  if not r:
    open(tag + '.drat', 'w').write('\n'.join(s.get_proof()) + '\n')
