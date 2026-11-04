"""
SAT thresholds: "least N such that every colouring / assignment of size N fails".

Pattern. Many book questions ask for the least N where some finite object
stops existing (Schur/Ramsey-type colourings, tilings, sign patterns,
sequences avoiding a pattern). Encode "object of size N exists" as CNF whose
clauses only grow with N, search N incrementally, then certify both sides:

* N-1 satisfiable: keep the model and re-check it with an independent
  checker written from the definition (not from the CNF);
* N unsatisfiable: re-solve with several different solvers and write a
  DRAT proof for an external checker (drat-trim / cake_lpr).

Used for: NT-E29.1 (x, y, x+y, xy monochromatic: N = 3150 from 3), NT-F6.1/F6.2
(Lehmer Q(a,b) for completely multiplicative +-1 functions), NT-E20.1
(Davenport-Schinzel lengths), GEO-C5.3 (incomparable cuboid tilings),
GEO-E4.4 (8-point order types).

`hyperedge_colouring` covers the common sub-case "2-colour [lo, N] with no
monochromatic hyperedge", where the hyperedges come from a user function.
"""
import gzip, os, time
from pysat.solvers import Solver
from pysat.formula import CNF

CROSS_CHECK = ('cadical153', 'glucose4', 'lingeling', 'minisat22', 'maplechrono')


def threshold(new_clauses, n_from, n_to, step=1, base=0, solver='cadical153', log=None):
  """Least N in [n_from, n_to] (stepping by step) with UNSAT.

  new_clauses(prev, N) returns the clauses that appear when the size grows
  from prev to N; the first call is new_clauses(base, n_from), so every
  clause of size <= n_from is included. Returns (N or None, last satisfying
  model, the N it belongs to).
  """
  s = Solver(name=solver)
  prev, model, sat_n = base, None, None
  t0 = time.time()
  try:
    for N in range(n_from, n_to + 1, step):
      for c in new_clauses(prev, N):
        s.add_clause(c)
      prev = N
      if s.solve():
        model, sat_n = s.get_model(), N
      else:
        if log:
          log('UNSAT at %d (%.1fs)' % (N, time.time() - t0))
        return N, model, sat_n
    return None, model, sat_n
  finally:
    s.delete()


def all_clauses(new_clauses, N, base=0):
  """Full clause list for size N (from scratch)."""
  return list(new_clauses(base, N))


def cross_check(clauses, names=CROSS_CHECK):
  """Solve with several solvers; returns {name: True/False}."""
  out = {}
  for n in names:
    with Solver(name=n, bootstrap_with=clauses) as s:
      out[n] = s.solve()
  return out


def write_certificate(clauses, path_prefix):
  """Write CNF and a DRAT proof (CaDiCaL), both gzipped. Returns UNSAT flag."""
  CNF(from_clauses=clauses).to_file(path_prefix + '.cnf')
  with Solver(name='cadical153', bootstrap_with=clauses, with_proof=True) as s:
    r = s.solve()
    proof = ( s.get_proof() if not r else [] )
  if not r:
    with open(path_prefix + '.drat', 'w') as f:
      f.write('\n'.join(proof) + '\n')
  for p in (path_prefix + '.cnf', path_prefix + '.drat'):
    if os.path.exists(p):
      with open(p, 'rb') as fi, gzip.open(p + '.gz', 'wb') as fo:
        fo.write(fi.read())
      os.remove(p)
  return not r


def hyperedge_colouring(edges, lo):
  """new_clauses for "2-colour [lo, N] with no monochromatic hyperedge".

  edges(prev, N) yields hyperedges (tuples of distinct integers in [lo, N])
  that are new when N grows from prev (typically: max element in (prev, N]).
  Variable v is the colour of integer v.
  """
  def new_clauses(prev, N):
    for e in edges(prev, N):
      yield list(e)
      yield [-v for v in e]
  return new_clauses


def check_colouring(colour, edges_all):
  """Independent witness check: no hyperedge monochromatic. Returns bad edges."""
  return [e for e in edges_all if len({colour[v] for v in e}) == 1]
