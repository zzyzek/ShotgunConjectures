"""
Carmichael numbers and Fermat pseudoprimes: criteria, families, data.

Patterns.

* Korselt reduction to a constant. If C = p * g(p) with g an integer
  polynomial, then C - 1 = g(1) - 1 (mod p - 1), so Korselt (p - 1 | C - 1)
  forces p - 1 | g(1) - 1: only finitely many p, listed by divisors. The same
  trick with ord_p(2) | C - 1 handles base-2 pseudoprimes. ("Infinitely many
  Carmichael numbers of the form p^4 + 60p" dies this way: p - 1 | 60.)
* Polynomial families (Chernick): C(k) = prod (a_i k + b_i) is Carmichael for
  every k with all factors prime iff each a_i k + b_i - 1 divides C(k) - 1 as
  integer-valued polynomials; `family_korselt` checks this exactly.
* Arithmetic progressions: Larsen (arXiv 2504.09056, 2025 preprint) gives a
  criterion for r mod M to contain infinitely many Carmichael numbers
  (`larsen_compatible`). Results that rely on it are conditional on the
  preprint; say so.
* Data: Feitsma-Galway base-2 pseudoprimes < 1e13 (annotated, Carmichael
  flagged) and Pinch's Carmichael list < 1e21 stream from data/.

Used for: COM-C116/C179/P055/P128, COM-C006, COM-C037/C076/C077/C128,
OEIS-A182085 family, A218010, A182090, COM-P019.
"""
import gzip, os
from math import gcd
import sympy as sp

# Repository root (oplib lives in methods/oplib/); tables are under data/.
#
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))


def korselt(n, factors=None):
  """True if n is a Carmichael number (squarefree, composite, p-1 | n-1)."""
  f = factors or sp.factorint(n)
  if len(f) < 2 or any(e > 1 for e in f.values()):
    return False
  return all((n - 1) % (p - 1) == 0 for p in f)


def is_psp(n, base=2):
  """Fermat pseudoprime to base: composite n with base^(n-1) = 1 mod n."""
  return (n > 2) and (pow(base, n - 1, n) == 1) and (not sp.isprime(n))


def korselt_constant(g):
  """For C = p * g(p) (g: sympy polynomial in one symbol), the constant K with
  'p | C Carmichael => p - 1 | K'. Returns K = g(1) - 1 (as int)."""
  x = list(g.free_symbols)[0]
  return int(g.subs(x, 1) - 1)


def candidates_from_constant(K):
  """Primes p with p - 1 | K (K != 0)."""
  K = abs(K)
  return sorted(d + 1 for d in sp.divisors(K) if sp.isprime(d + 1))


def family_korselt(factors, k):
  """factors: sympy linear/polynomial expressions in k. True if every factor
  f - 1 divides prod(f) - 1 for all integers k (polynomial division with an
  integer-valued quotient), i.e. the family is Carmichael whenever all factors
  are prime (and distinct)."""
  N = sp.expand(sp.prod(factors))
  for f in factors:
    q, r = sp.div(sp.Poly(N - 1, k), sp.Poly(f - 1, k))
    if not r.is_zero:
      return False
    qe = q.as_expr()
    deg = sp.Poly(qe, k).degree()
    if not all(qe.subs(k, t).is_integer for t in range(deg + 1)):
      return False
  return True


def larsen_compatible(r, M):
  """Larsen's criterion (arXiv 2504.09056): r mod M contains infinitely many
  Carmichael numbers. Conditional on that preprint."""
  g = gcd(r, M)
  h = gcd(int(sp.reduced_totient(g)), M)
  c3 = (M % 36 == 0) and (r % 12 == 3) and ((r // g) % 12 in (5, 7))
  return (gcd(g, 2 * int(sp.totient(g))) == 1) and ((r - 1) % h == 0) and (not c3)


def stream_psp2(path=None, carmichael_only=False):
  """Yield (n, prime factors, is_carmichael) for base-2 pseudoprimes < 1e13
  from the Feitsma-Galway annotated list. Line format: '[C] n p1 p2 ...',
  with 'C' marking Carmichael numbers."""
  path = path or os.path.join(ROOT, 'data', 'psp2-annot-below-1e13.txt')
  with open(path) as f:
    for line in f:
      t = line.split()
      if not t:
        continue
      carm = ( t[0] == 'C' )
      if carm:
        t = t[1:]
      if (not t) or (not t[0].isdigit()):
        continue
      if carmichael_only and (not carm):
        continue
      yield int(t[0]), [int(x) for x in t[1:]], carm


def stream_carmichael(path=None):
  """Yield Carmichael numbers < 1e21 from Pinch's list (one per line, gz)."""
  path = path or os.path.join(ROOT, 'data', 'pinch', 'c21.gz')
  with gzip.open(path, 'rt') as f:
    for line in f:
      t = line.split()
      if t and t[0].isdigit():
        yield int(t[0])
