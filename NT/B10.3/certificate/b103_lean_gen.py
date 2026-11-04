#!/usr/bin/env python3
"""Generate NT/B10.3/B10_3_mathlib.lean from certificate/B10_3_mathlib.lean.tmpl.

Tables (all re-checked by the Lean kernel): factorizations of n = 1..2520 (W(n) for small n),
of k² for odd composite 51 ≤ k < 672, and a witness n with W(n) = m for every odd m < 1000
that is a value of W. Needs sympy.  Usage: python3 NT/B10.3/certificate/b103_lean_gen.py
"""
import os
from sympy import factorint, isprime, divisor_count, totient

HERE = os.path.dirname(os.path.abspath(__file__))


def fl(n):
  return "[" + ", ".join("(%d, %d)" % (p, e) for p, e in sorted(factorint(n).items())) + "]"


def W(n):
  return n - divisor_count(n) - totient(n) + 1


first = {}
for n in range(1, 2521):
  first.setdefault(W(n), n)
L, wit = [], []
for m in range(1, 1000, 2):
  if m in first:
    wit.append((m, first[m]))
  elif isprime(m + 2):
    wit.append((m, (m + 2) ** 2))
  else:
    L.append(m)
assert len(L) == 86

tabS = ",\n   ".join(fl(n) for n in range(1, 2521))
T2 = ",\n   ".join("(%d, %s)" % (k, fl(k * k)) for k in range(51, 672, 2) if not isprime(k))
Wt = ",\n   ".join("(%d, %s)" % (m, fl(n)) for m, n in wit)
src = open(os.path.join(HERE, "B10_3_mathlib.lean.tmpl")).read()
Lf = ", ".join("(%d, %d)" % (m, min(factorint(m + 2))) for m in L)
src = (src.replace("@LIST", ", ".join(map(str, L))).replace("@LF", Lf).replace("@TABS", tabS)
          .replace("@T2", T2).replace("@WIT", Wt))
open(os.path.join(HERE, "..", "B10_3_mathlib.lean"), "w").write(src)
print("L", len(L), "witnesses", len(wit))
