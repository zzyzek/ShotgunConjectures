#!/usr/bin/env python3
"""Lean proof that a Chernick-type product of linear factors is a Carmichael number
whenever all its factors are prime (uses lib/OpenProblemsLib, Korselt's criterion).

  family_lean.py NAME "a1,c1 a2,c2 ..."

prints a Lean theorem

  theorem NAME (n : ℕ) (h1 : (a1 * n ± |c1|).Prime) ... :
      ((a1 * n ± |c1|) * (a2 * n ± |c2|) * ...).IsCarmichael

(natural-number subtraction for negative c; the primality hypotheses force n large
enough that nothing is truncated). For each factor f, N - 1 = (f - 1) Q(k) with an
explicit polynomial Q (found by sympy, after the shift n = k + S that makes every
factor's constant term positive); `ring` checks the identity in Lean.
"""
import sys
from sympy import symbols, Poly, div, expand


def term(a, c, v):
  if c >= 0:
    return "%d * %s + %d" % (a, v, c)
  return "%d * %s - %d" % (a, v, -c)


def lean_poly(p, v):
  # Natural-coefficient polynomial in v, as a Lean expression.
  #
  cs = Poly(p, symbols(v)).all_coeffs()
  deg = len(cs) - 1
  parts = []
  for i, c in enumerate(cs):
    e = deg - i
    c = int(c)
    if c < 0:
      raise ValueError("negative coefficient")
    if c == 0:
      continue
    if e == 0:
      parts.append("%d" % c)
    elif e == 1:
      parts.append("%d * %s" % (c, v))
    else:
      parts.append("%d * %s ^ %d" % (c, v, e))
  return " + ".join(parts) if parts else "0"


def theorem(name, fs):
  k = symbols("k")
  m = len(fs)

  # Shift S: smallest n with a n + c >= 1 for every factor.
  #
  S = 0
  while any((a * S + c) < 1 for a, c in fs):
    S += 1
  sh = [(a, a * S + c) for a, c in fs]
  N  = 1
  for a, b in sh:
    N *= (a * k + b)
  N = expand(N)

  qs = []
  for a, b in sh:
    q, r = div(Poly(N - 1, k), Poly(a * k + b - 1, k))
    if not r.is_zero:
      raise ValueError("factor %d k + %d: f - 1 does not divide N - 1" % (a, b))
    qs.append(lean_poly(q.as_expr(), "k"))

  F  = [term(a, c, "n") for a, c in fs]
  v  = "k" if S > 0 else "n"
  G  = ["%d * %s + %d" % (a, v, b) for a, b in sh]
  L  = []
  hs = " ".join("(h%d : (%s).Prime)" % (i + 1, f) for i, f in enumerate(F))
  L.append("theorem %s (n : ℕ) %s :" % (name, hs))
  L.append("    (%s).IsCarmichael := by" % " * ".join("(%s)" % f for f in F))
  if S > 0:
    for i in range(m):
      L.append("  have l%d := h%d.two_le" % (i + 1, i + 1))
    L.append("  obtain ⟨k, rfl⟩ : ∃ k, n = k + %d := ⟨n - %d, by omega⟩" % (S, S))
    for i, (a, c) in enumerate(fs):
      src = term(a, c, "(k + %d)" % S)
      L.append("  have e%d : %s = %s := by omega" % (i + 1, src, G[i]))
    for i in range(m):
      L.append("  rw [e%d] at h%d" % (i + 1, i + 1))
    L.append("  rw [%s]" % ", ".join("e%d" % (i + 1) for i in range(m)))
  L.append("  apply isCarmichael_of_factors _ [%s]" % ", ".join(G))
  alts = " | ".join(["rfl"] * m)
  L.append("  · simp only [List.mem_cons, List.not_mem_nil, or_false]")
  L.append("    rintro p (%s)" % alts)
  L.append("    exacts [%s]" % ", ".join("h%d" % (i + 1) for i in range(m)))
  L.append("  · simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,")
  L.append("      List.nodup_nil, not_false_eq_true, and_true]")
  L.append("    omega")
  L.append("  · simp only [List.prod_cons, List.prod_nil, mul_one, mul_assoc]")
  L.append("  · simp")
  L.append("  · simp only [List.mem_cons, List.not_mem_nil, or_false]")
  L.append("    rintro p (%s)" % alts)
  for i, (a, b) in enumerate(sh):
    L.append("    · refine dvd_sub_one_of_eq (Q := %s) ?_" % qs[i].replace("k", v))
    L.append("      rw [show %s - 1 = %d * %s + %d by omega]" % (G[i], a, v, b - 1))
    L.append("      ring")
  return "\n".join(L)


if __name__ == "__main__":
  fs = [tuple(int(x) for x in f.split(",")) for f in sys.argv[2].split()]
  print(theorem(sys.argv[1], fs))
