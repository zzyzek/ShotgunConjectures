#!/usr/bin/env python3
"""Generate NT/A3.9/A3_9_mathlib.lean: p(k) = least prime with digit sum k, 25 < k < 180,
k not a multiple of 3, with a Pratt certificate for every p(k) and one proper factor of every
smaller number with digit sum k (the Lean kernel re-enumerates those numbers itself, with
the verified enumerator chkF, and checks each factor).

Usage (from the repo root): python3 NT/A3.9/certificate/a39_lean_gen.py
Needs sympy (factorint) for the factors and for tools/pratt_cert.py.
"""
import os, sys
ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", "..", ".."))
sys.path.insert(0, os.path.join(ROOT, "tools"))
from pratt_cert import steps, lean_list
from sympy import isprime, factorint


def gen(L, k):
  # L-digit numbers with digit sum k, increasing.
  #
  def rec(pos, rem, first):
    if pos == L:
      if rem == 0:
        yield 0
      return
    for d in range(1 if first else 0, 10):
      r = rem - d
      if 0 <= r <= 9 * (L - pos - 1):
        for t in rec(pos + 1, r, False):
          yield d * 10 ** (L - pos - 1) + t
  return rec(0, k, True)


def pk(k):
  # (p(k), factors of all smaller numbers with digit sum k)
  #
  L, fs = (k + 8) // 9, set()
  while True:
    for n in gen(L, k):
      if isprime(n):
        return n, sorted(fs)
      fs.add(min(factorint(n)))
    L += 1


ks = [k for k in range(26, 180) if k % 3 != 0]
rows = [(k,) + pk(k) for k in ks]
cert = steps([P for _, P, _ in rows])

tab = ",\n   ".join("(%d, %d, [%s])" % (k, P, ", ".join(map(str, fs))) for k, P, fs in rows)
src = open(os.path.join(os.path.dirname(__file__), "A3_9_mathlib.lean.tmpl")).read()
src = src.replace("@CERT", lean_list(cert, "   ")).replace("@TABLE", tab)
open(os.path.join(ROOT, "NT", "A3.9", "A3_9_mathlib.lean"), "w").write(src)
print("rows", len(rows), "factors", sum(len(f) for _, _, f in rows), "cert steps", len(cert))
