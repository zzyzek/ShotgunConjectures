#!/usr/bin/env python3
"""Expand certificate macros in a Lean template that imports OpenProblemsLib.

Usage: lean_expand.py TEMPLATE OUT.lean

Macro lines (each on its own line, starting at column 0):
  @CERT                       the shared Pratt certificate `cert` for every prime named
                              by the macros below (must come before them)
  @CARM name n p1 p2 ...      theorem name : Nat.IsCarmichael n   (Korselt, primes certified)
  @PRIMES name p1 p2 ...      theorem name : ∀ p ∈ [p1, ...], Nat.Prime p
  @PRIME name p               theorem name : Nat.Prime p
  @FACT name n p1 p2 ...      theorem name : Squarefree n ∧ n.primeFactors = {p1, p2, ...}
                              (n = p1 * p2 * ..., distinct certified primes)
  @FAMILY name a1,c1 a2,c2 ...
                              theorem name: if every a_i n + c_i is prime then the product
                              is Carmichael (tools/family_lean.py)
  @CORE path                  the core-Lean file `path` (relative to the template's
                              directory), without its header comment, inside
                              `namespace Core ... end Core` (indented); its theorems are
                              available as `Core.name`

Numbers may be written as Python integer expressions without spaces (e.g. 2**61-1);
they are evaluated and printed as decimal literals. The Pratt certificate comes from
tools/pratt_cert.py (sympy); the Lean kernel checks it by `decide +kernel`.
"""
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from pratt_cert import steps, lean_list
from family_lean import theorem as family_theorem


def num(s):
  return int(eval(s, {"__builtins__": {}}, {}))


def main(src, dst):
  lines  = open(src).read().split("\n")
  primes = []
  for ln in lines:
    w = ln.split()
    if not w:
      continue
    if w[0] in ("@CARM", "@FACT"):
      primes += [num(x) for x in w[3:]]
    elif w[0] in ("@PRIMES", "@PRIME"):
      primes += [num(x) for x in w[2:]]

  out = []
  for ln in lines:
    w = ln.split()
    if (not w) or (not w[0].startswith("@")):
      out.append(ln)
      continue
    tag = w[0]
    if tag == "@FAMILY":
      out.append(family_theorem(w[1], [tuple(int(x) for x in f.split(",")) for f in w[2:]]))
    elif tag == "@CORE":
      path = os.path.join(os.path.dirname(os.path.abspath(src)), w[1])
      body = open(path).read()
      if body.lstrip().startswith("/-") and not body.lstrip().startswith("/-!"):
        body = body[body.index("-/") + 2:]
      out.append("/-! ### Core-Lean facts, copied verbatim from `%s` -/" % os.path.basename(path))
      out.append("namespace Core")
      # Indented two spaces so that the check script's `#print axioms` pass (which
      # looks for column-0 `theorem`) only reports this file's own theorems.
      #
      out += [("  " + x) if x.strip() else "" for x in body.strip("\n").split("\n")]
      out.append("end Core")
    elif tag == "@CERT":
      out.append("/-- Pratt certificate for every prime used below (tools/pratt_cert.py). -/")
      out.append("def cert : List PrattStep :=")
      out.append("  " + lean_list(steps(sorted(set(primes))), indent="   "))
    elif tag == "@CARM":
      n, ps = num(w[2]), [num(x) for x in w[3:]]
      assert eval("*".join(map(str, ps))) == n, (n, ps)
      out.append("theorem %s : Nat.IsCarmichael %d :=" % (w[1], n))
      out.append("  isCarmichael_of_carmichaelCheck %d [%s] cert (by decide +kernel)"
                 % (n, ", ".join(map(str, ps))))
    elif tag == "@PRIMES":
      ps = [num(x) for x in w[2:]]
      out.append("theorem %s : ∀ p ∈ [%s], Nat.Prime p :=" % (w[1], ", ".join(map(str, ps))))
      out.append("  primes_of_prattCertifiesAll _ cert (by decide +kernel)")
    elif tag == "@PRIME":
      p = num(w[2])
      out.append("theorem %s : Nat.Prime %d :=" % (w[1], p))
      out.append("  prime_of_prattCertifies _ cert (by decide +kernel)")
    elif tag == "@FACT":
      n, ps = num(w[2]), [num(x) for x in w[3:]]
      assert eval("*".join(map(str, ps))) == n, (n, ps)
      out.append("theorem %s : Squarefree %d ∧ Nat.primeFactors %d = {%s} := by"
                 % (w[1], n, n, ", ".join(map(str, ps))))
      out.append("  have h := squarefree_of_factorCheck %d [%s] cert (by decide +kernel)"
                 % (n, ", ".join(map(str, ps))))
      out.append("  exact ⟨h.1, by rw [h.2]; decide⟩")
    else:
      raise ValueError("unknown macro " + tag)
  open(dst, "w").write("\n".join(out))


if __name__ == "__main__":
  main(sys.argv[1], sys.argv[2])
