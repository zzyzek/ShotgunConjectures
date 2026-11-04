"""
Finite verification of sequence identities ("agree on enough terms => equal").

Pattern. Most OEIS formula conjectures say two descriptions of a sequence
agree. When both sides lie in a class with a size bound, agreement on finitely
many terms is a proof:

* C-finite (linear recurrence, constant coefficients): if f has order <= d1
  and g order <= d2, then f - g has order <= d1 + d2, so agreement on d1 + d2
  consecutive terms (from where both recurrences hold) proves f = g.
  Rational g.f.s are the same thing (order = max(deg num + 1, deg den)).
* Quasi-polynomials of degree <= d and period P: agreement on (d + 1) * P
  consecutive terms.
* Polynomial identities in a parameter m of degree <= d: d + 1 values of m.
* P-recursive (holonomic): closure bounds exist but are large; in practice
  guess a recurrence, then prove it for each side (e.g. creative telescoping)
  and fall back to the C-finite style argument with the leading coefficient's
  roots excluded.

The step that needs a proof is that each side really satisfies its claimed
recurrence; the library checks the finite part and says what it assumed.

Used for: OEIS-A107363 (rational g.f. 6-sections), A110320 (g.f. difference
= 0), A113249 family (identity in Z[m] via a common annihilator), A124431
(holonomic), A008676 (quasi-polynomial, period 15), A182334 (Pell-type order-9
recurrence, exact failure at n = 10).
"""
from fractions import Fraction
from math import lcm
import sympy as sp


def series_div(num, den, n):
  """First n coefficients of num(x)/den(x) (lists, low degree first), exact."""
  num = [Fraction(c) for c in num] + [Fraction(0)] * n
  den = [Fraction(c) for c in den]
  if den[0] == 0:
    raise ValueError('den(0) must be nonzero')
  out = []
  for k in range(n):
    c = num[k]
    for j in range(1, min(k, len(den) - 1) + 1):
      c -= den[j] * out[k - j]
    out.append(c / den[0])
  return [ ( int(c) if c.denominator == 1 else c ) for c in out ]


def berlekamp_massey(seq):
  """Minimal linear recurrence over Q: returns coefficients c with
  s[n] = c[0] s[n-1] + ... + c[L-1] s[n-L] for all n >= L (on the given data)."""
  s = [Fraction(x) for x in seq]
  C, B = [Fraction(1)], [Fraction(1)]
  L, m, b = 0, 1, Fraction(1)
  for n in range(len(s)):
    d = s[n] + sum(C[i] * s[n - i] for i in range(1, L + 1))
    if d == 0:
      m += 1
      continue
    T = list(C)
    coef = d / b
    C = C + [Fraction(0)] * max(0, len(B) + m - len(C))
    for i, bi in enumerate(B):
      C[i + m] -= coef * bi
    if 2 * L <= n:
      L, B, b, m = n + 1 - L, T, d, 1
    else:
      m += 1
  return [-c for c in C[1:L + 1]]


def guess_recurrence(seq, margin=8):
  """BM guess, accepted only if it predicts `margin` terms beyond 2*order."""
  c = berlekamp_massey(seq)
  if (2 * len(c) + margin) > len(seq):
    return None
  for n in range(len(c), len(seq)):
    if sum(ci * seq[n - 1 - i] for i, ci in enumerate(c)) != seq[n]:
      return None
  return c


def apply_recurrence(c, init, n):
  """Extend init with recurrence c to n terms."""
  s = list(init)
  while len(s) < n:
    s.append(sum(ci * s[-1 - i] for i, ci in enumerate(c)))
  return s


def first_failure(c, seq, start=None):
  """First index n (>= start, default len(c)) where seq violates recurrence c."""
  k = len(c)
  for n in range(start if start is not None else k, len(seq)):
    if sum(ci * seq[n - 1 - i] for i, ci in enumerate(c)) != seq[n]:
      return n
  return None


def c_finite_equal(f, g, d1, d2, start=0):
  """Prove f = g from start on, given f, g satisfy linear recurrences of order
  <= d1, d2 there (assumption, stated by caller). Checks d1 + d2 terms."""
  N = d1 + d2
  bad = [n for n in range(start, start + N) if f(n) != g(n)]
  return ( not bad ), { 'checked': (start, start + N - 1), 'mismatch': bad,
                        'assumes': 'both sides satisfy recurrences of order <= %d, %d' % (d1, d2) }


def quasipoly_equal(f, g, degree, period, start=0):
  """Prove f = g where both are quasi-polynomials of degree <= degree, period | period."""
  N = (degree + 1) * period
  bad = [n for n in range(start, start + N) if f(n) != g(n)]
  return ( not bad ), { 'checked': (start, start + N - 1), 'mismatch': bad }


def poly_identity_in_param(F, m, deg_bound, values=None):
  """F(m) a sympy expression claimed identically 0 as a polynomial of degree <= deg_bound.
  Symbolic expand first; if not obviously 0, check deg_bound + 1 integer values."""
  e = sp.expand(F)
  if e == 0:
    return True, 'expands to 0'
  vals = values or list(range(deg_bound + 1))
  bad = [v for v in vals if sp.simplify(e.subs(m, v)) != 0]
  return ( not bad ), ( 'nonzero at %s' % bad if bad else 'zero at %d points' % len(vals) )


def guess_p_recursive(seq, order, degree, offset=0):
  """Guess sum_{i<=order} p_i(n) a(n-i) = 0 with deg p_i <= degree (over Q).
  Returns list of coefficient polynomials (sympy) or None. Needs enough terms:
  unknowns (order+1)(degree+1) - 1 plus a margin of 8 equations."""
  n = sp.symbols('n')
  unknowns = (order + 1) * (degree + 1)
  rows = []
  for k in range(order, len(seq)):
    N = k + offset
    rows.append([ sp.Integer(N) ** j * sp.Integer(seq[k - i]) for i in range(order + 1) for j in range(degree + 1) ])
  if len(rows) < unknowns + 8:
    return None
  ns = sp.Matrix(rows).nullspace()
  if len(ns) != 1:
    return None
  v = ns[0]
  den = lcm(*[ int(sp.fraction(x)[1]) for x in v ])
  v = [ x * den for x in v ]
  return [ sum(v[i * (degree + 1) + j] * n ** j for j in range(degree + 1)) for i in range(order + 1) ]
