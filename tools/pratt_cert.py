#!/usr/bin/env python3
"""Pratt primality certificates for lib/OpenProblemsLib/Pratt.lean.

Usage:
  pratt_cert.py N [N ...]        print a Lean term `[⟨p, a, [(q, k), ...]⟩, ...]`
                                 certifying every N (and every prime it needs)

As a library: `steps(ns)` returns the ordered steps (p, a, [(q, k), ...]),
`lean_list(steps)` formats them. Every q of a step is the p of an earlier step,
and the list starts with (2, 1, []), as prattCheck requires.

Factoring of p - 1 uses sympy (run with the repo's .venv python); the
certificate itself is checked independently by the Lean kernel.
"""
import sys
from sympy import factorint, isprime


def witness(p, qs):
  # Smallest a with a^(p-1) = 1 and a^((p-1)/q) != 1 (mod p) for all q.
  #
  if p == 2:
    return 1
  a = 2
  while True:
    if ( (pow(a, p - 1, p) == 1) and
         all(pow(a, (p - 1) // q, p) != 1 for q in qs) ):
      return a
    a += 1


def steps(ns):
  done  = {}
  order = []

  def add(p):
    if p in done:
      return
    if not isprime(p):
      raise ValueError("%d is not prime" % p)
    fs = sorted(factorint(p - 1).items()) if p > 2 else []
    for q, _ in fs:
      add(q)
    a = witness(p, [q for q, _ in fs])
    done[p] = (p, a, fs)
    order.append(done[p])

  add(2)
  for n in ns:
    add(n)
  return order


def lean_list(st, indent="  "):
  rows = []
  for p, a, fs in st:
    f = ", ".join("(%d, %d)" % (q, k) for q, k in fs)
    rows.append("⟨%d, %d, [%s]⟩" % (p, a, f))
  return "[" + (",\n" + indent).join(rows) + "]"


if __name__ == "__main__":
  print(lean_list(steps([int(x) for x in sys.argv[1:]])))
