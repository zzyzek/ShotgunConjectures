"""
Covering congruences: show a family F(n) = A*b^n + C (n >= n0) is never prime.

Pattern. For a prime q with o = ord_q(b), "q | F(n)" depends only on n mod o,
and holds on at most one class n = a (mod o) (when q does not divide A).
If the classes chosen for several primes cover every residue mod
L = lcm(o_i), every F(n) has a factor from the set, and is composite once
F(n) exceeds that factor. Sierpinski/Riesel numbers are the classic case.

Two directions are used in practice:

* fixed family, find the cover (is this specific F(n) always composite?):
  `classes_for_family` + `find_cover`;
* free parameter x, find x with an always-composite family (disprove
  "for every x there is a prime ..."): the condition q | F(x, a) must be one
  residue class of x mod q (true when F is affine in x); `solve_parameter`
  picks a cover, solves the classes by CRT, then searches the progression
  for x satisfying extra conditions (e.g. x prime, x a Poulet number).

Used for: COM-C125 (5p + 2^n), COM-C128 / C127 ((P + 5^m)/10), OEIS-A176494
(|2^m - p|), A088276 (10^k + r), A133832, A229927.

Certificates are plain dicts and are re-checked by `verify`.
"""
from math import gcd, lcm
from sympy import factorint, n_order, isprime
from sympy.ntheory.modular import crt


def primes_with_order_dividing(b, L, exclude=()):
  """Primes q (not dividing b, not in exclude) with ord_q(b) | L, as {q: ord}.

  Every such q divides b^L - 1, so factoring b^L - 1 finds them all.
  Factoring is the cost; keep L modest (<= ~ 200 for b = 2).
  """
  out = {}
  for q in factorint(b ** L - 1):
    if (q in exclude) or (b % q == 0):
      continue
    out[q] = n_order(b, q)
  return out


def dlog(b, x, q, o):
  """Least c in [0, o) with b^c = x (mod q), or None. Linear scan (o small)."""
  x %= q
  v = 1
  for c in range(o):
    if v == x:
      return c
    v = (v * b) % q
  return None


def classes_for_family(A, b, C, primes):
  """For F(n) = A*b^n + C: list of (q, o, a) with q | F(n) iff n = a (mod o)."""
  out = []
  for q, o in primes.items():
    if A % q == 0:
      continue
    target = (-C * pow(A, -1, q)) % q
    a = dlog(b, target, q, o)
    if a is not None:
      out.append((q, o, a))
  return out


def covers(classes, L):
  """True if the classes (q, o, a) cover every residue mod L."""
  hit = [False] * L
  for (q, o, a) in classes:
    for n in range(a % o, L, o):
      hit[n] = True
  return all(hit)


def find_cover(options, L, max_nodes=200000):
  """Choose at most one class per prime so the classes cover Z/L.

  options: list of (q, o, [allowed classes a]). Greedy by coverage with
  backtracking (bounded by max_nodes). Returns a list of (q, o, a) or None.
  """
  opts = sorted(options, key=lambda t: t[1])
  best = [None]
  nodes = [0]

  def rec(unc, i, chosen):
    nodes[0] += 1
    if not unc:
      best[0] = list(chosen)
      return True
    if (i >= len(opts)) or (nodes[0] > max_nodes):
      return False

    # Branch on the uncovered residue with the fewest remaining options,
    # trying classes that cover it, most coverage first.
    #
    r = min(unc)
    cand = []
    for j in range(i, len(opts)):
      q, o, cls = opts[j]
      if any(c for c in chosen if c[0] == q):
        continue
      if (r % o) in [a % o for a in cls]:
        a = r % o
        cnt = sum(1 for u in unc if u % o == a)
        cand.append((cnt, q, o, a))
    cand.sort(reverse=True)
    for cnt, q, o, a in cand:
      chosen.append((q, o, a))
      if rec({u for u in unc if u % o != a}, i, chosen):
        return True
      chosen.pop()
    return False

  rec(set(range(L)), 0, [])
  return best[0]


def solve_parameter(b, L, residue_for, extra=(), accept=None, exclude=(), limit=10 ** 6):
  """Find x with q | F(x, n) on a covering of n mod L.

  residue_for(q, a) -> residue r of x mod q making q | F(x, n) for all
                       n = a (mod ord_q(b)), or None if impossible.
  extra            -> further congruences [(r, m)] on x (e.g. x = 5 mod 10).
  accept(x)        -> extra predicate searched along the progression.
  Returns a certificate dict or None.
  """
  P = primes_with_order_dividing(b, L, exclude)
  options = []
  for q, o in P.items():
    cls = [a for a in range(o) if residue_for(q, a) is not None]
    if cls:
      options.append((q, o, cls))
  cover = find_cover(options, L)
  if cover is None:
    return None
  mods = [q for (q, o, a) in cover] + [m for (r, m) in extra]
  res  = [residue_for(q, a) for (q, o, a) in cover] + [r for (r, m) in extra]
  r0, M = crt(mods, res)
  r0, M = int(r0), int(M)
  x = r0
  for _ in range(limit):
    if (x > 0) and ((accept is None) or accept(x)):
      return { 'b': b, 'L': L, 'cover': cover, 'progression': (r0, M), 'x': x }
    x += M
  return { 'b': b, 'L': L, 'cover': cover, 'progression': (r0, M), 'x': None }


def verify(cert, F, n0=1, small_check=None):
  """Check a covering certificate against the family F(n) (exact integers).

  * every n mod L is covered by some (q, o, a) with q | F(n), checked on
    n = n0 .. n0 + 3L (the classes are periodic, so this is the whole proof
    of divisibility once ord_q(b) = o is confirmed);
  * F(n) > max q for n >= n0 + small_check, and F(n) composite directly
    below that (pass small_check = number of initial n to test by isprime).
  Returns (ok, message).
  """
  b, L, cover = cert['b'], cert['L'], cert['cover']
  for (q, o, a) in cover:
    if n_order(b, q) != o:
      return False, 'order mismatch at q=%d' % q
  if not covers(cover, L):
    return False, 'classes do not cover Z/%d' % L
  qmax = max(q for (q, o, a) in cover)
  for n in range(n0, n0 + 3 * L):
    v = F(n)
    if not any((v % q == 0) for (q, o, a) in cover if n % o == a % o):
      return False, 'n=%d: assigned prime does not divide F(n)' % n
  k = small_check or 0
  for n in range(n0, n0 + k):
    v = abs(F(n))
    if (v > 1) and isprime(v):
      return False, 'F(%d) is prime' % n
  return True, 'covering mod %d with %d primes; max prime %d' % (L, len(cover), qmax)
