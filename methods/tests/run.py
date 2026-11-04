#!/usr/bin/env python3
# Regression tests for oplib: each test reproduces a result already
# established in the scan, so a library change that breaks a method shows up
# as a known answer going wrong. Light: seconds, single process.
#
# Usage (from methods/): python3 -I tests/run.py [name ...]   (needs sympy, python-sat)
#
import os, sys, time, traceback

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, ROOT)

import sympy as sp
from oplib import covering, sat, seqtools, carmichael, modular, exact, tiling, lean


def test_covering_c125():
  # COM-C125: 5p + 2^n composite for all n >= 1, p = 76739471787787.
  #
  p = 76739471787787
  P = covering.primes_with_order_dividing(2, 72, exclude=(5,))
  cl = covering.classes_for_family(1, 2, 5 * p, P)
  cover = covering.find_cover([(q, o, [a]) for (q, o, a) in cl], 72)
  assert cover is not None
  ok, msg = covering.verify({ 'b': 2, 'L': 72, 'cover': cover }, lambda n: 5 * p + 2 ** n, n0=1, small_check=40)
  assert ok, msg
  assert sp.isprime(p)


def test_covering_parameter_a176494():
  # A176494 shape: odd prime x with |2^m - x| composite for all m >= 1
  # (q | 2^m - x iff x = 2^a mod q on the class m = a mod ord_q 2).
  #
  cert = covering.solve_parameter(2, 24, lambda q, a: pow(2, a, q), extra=[(1, 2)],
                                  accept=lambda x: (x > 1000) and sp.isprime(x), limit=200000)
  assert cert and cert['x']
  x = cert['x']
  ok, msg = covering.verify(cert, lambda m: abs(2 ** m - x), n0=1, small_check=x.bit_length() + 30)
  assert ok, msg


def test_covering_c128_classes():
  # COM-C128: the eight classes of m mod 36 via ord_q(5).
  #
  cov = [(7, 6, 1), (13, 4, 0), (19, 9, 2), (31, 3, 0), (37, 36, 26), (601, 12, 10), (829, 9, 5), (5167, 18, 17)]
  assert all(sp.n_order(5, q) == o for q, o, a in cov)
  assert covering.covers(cov, 36)


def test_sat_graham_252():
  # Graham: every 2-colouring of [1, N] has x < y with x, y, x+y, xy in one
  # class iff N >= 252 (Guy E29). For x = 1 the set is {1, y, y+1}; Guy's
  # "four distinct numbers" wording is loose here. The same x < y convention
  # gives Hindman's 990 on [2, N] and NT-E29.1's 3150 on [3, N] (for lo >= 2
  # the four numbers are automatically distinct). Allowing x = y changes the
  # answers (39 on [1, N], 450 on [2, N]).
  #
  lo = 1
  def edges(prev, N):
    for x in range(lo, N + 1):
      for y in range(x + 1, N // x + 1):
        p, q = x * y, x + y
        if prev < max(p, q) <= N:
          yield tuple(sorted({x, y, q, p}))
  N, model, satN = sat.threshold(sat.hyperedge_colouring(edges, lo), 200, 300, base=0)
  assert N == 252, N
  col = { abs(v): (v > 0) for v in model }
  alle = list(edges(0, satN))
  assert not sat.check_colouring({ v: col.get(v, False) for v in range(lo, satN + 1) }, alle)


def test_seq_bm_and_failure():
  # A182334: the printed order-9 recurrence fails first at a(10) (offset 1).
  #
  a = [0, 1, 3, 10, 15, 120, 325, 528, 4095, 11026, 17955, 139128, 374545, 609960, 4726275]
  c = [0, 0, 35, 0, 0, -35, 0, 0, 1]
  assert seqtools.first_failure(c, a) == 9
  fib = [0, 1]
  for _ in range(30):
    fib.append(fib[-1] + fib[-2])
  assert seqtools.guess_recurrence(fib) == [1, 1]


def test_seq_quasipoly_a008676():
  # A008676: coefficients of 1/((1-x^3)(1-x^5)) = floor(2(n+3)/3) - floor(3(n+3)/5).
  #
  co = seqtools.series_div([1], [1, 0, 0, -1, 0, -1, 0, 0, 1], 200)
  ok, info = seqtools.quasipoly_equal(lambda n: co[n], lambda n: (2 * (n + 3)) // 3 - (3 * (n + 3)) // 5, 1, 15)
  assert ok, info


def test_carmichael():
  assert carmichael.korselt(561) and (not carmichael.korselt(341))
  p = sp.symbols('p')
  K = carmichael.korselt_constant(p ** 3 + 60)
  cand = carmichael.candidates_from_constant(K)
  hits = [q for q in cand if carmichael.korselt(q ** 4 + 60 * q)]
  assert hits == [7, 13], hits
  k = sp.symbols('k')
  assert carmichael.family_korselt([6 * k + 1, 12 * k + 1, 18 * k + 1], k)
  assert not carmichael.family_korselt([6 * k + 1, 12 * k + 1, 18 * k + 5], k)


def test_modular_factorial():
  # NT-F23.2: n! = 2^a + 2^b impossible for n >= 7 (mod 7).
  #
  m = modular.obstruct(lambda m: {0},
                       lambda m: modular.sumset(modular.residues_power(2, m), modular.residues_power(2, m), m),
                       [3, 5, 7])
  assert m == 7


def test_exact_a100682():
  from math import comb
  n = 634027531
  assert exact.iroot(comb(n, 4), 4) == 286454272
  assert exact.floor_ratio_root(2 * n - 3, 2, 24, 4) == 286454273


def test_tiling_c22():
  sq = [(402, 0, 0), (397, 402, 0), (5, 402, 397), (28, 407, 397), (72, 435, 397), (292, 507, 397),
        (287, 0, 402), (67, 287, 402), (30, 354, 402), (23, 384, 402), (7, 384, 425), (44, 391, 425),
        (37, 354, 432), (220, 287, 469)]
  assert tiling.check_tiling(799, 689, sq) and tiling.is_perfect(sq)


def test_lean_emit():
  f = lean.LeanFile('oplib self-test')
  f.eq('d22', '17 ^ 3 + 37 ^ 3', '6 * 21 ^ 3')
  f.factor('c187', 187, 11)
  path = f.write(os.path.join(ROOT, 'tests', '_selftest.lean'))
  ok, out = lean.check(path)
  os.remove(path)
  assert ok and ('does not depend on any axioms' in out), out


TESTS = [ (k, v) for k, v in sorted(globals().items()) if k.startswith('test_') ]

if __name__ == '__main__':
  pick = set(sys.argv[1:])
  fails = 0
  for name, fn in TESTS:
    if pick and (name not in pick):
      continue
    t = time.time()
    try:
      fn()
      print('ok    %-34s %.1fs' % (name, time.time() - t), flush=True)
    except Exception:
      fails += 1
      print('FAIL  %-34s %.1fs' % (name, time.time() - t), flush=True)
      traceback.print_exc()
  print('%d failed' % fails)
  sys.exit(1 if fails else 0)
