#!/usr/bin/env python3
# Assemble A187011_growth_mathlib.lean, one file for tools/leancheck-mathlib.sh:
#   1. FAM/twin-primes/twin_primes_mathlib.lean (itself assembled by
#      FAM/twin-primes/certificate/assemble.py: the PrimeNumberTheoremAnd
#      Selberg sieve files, Apache 2.0, copyright headers kept, plus the
#      prime-pair bound pairCount_le_log), imports hoisted;
#   2. OEIS/A187011/A187011_mathlib.lean (determinant formula and sign),
#      its import and leading header comment dropped;
#   3. certificate/Growth.lean.part (the growth half).
# The header comment of the output is certificate/header.lean.part.
#
# Usage: assemble.py <out.lean>   (run from anywhere)
#
import os, sys

here = os.path.dirname(os.path.abspath(__file__))
repo = os.path.normpath(os.path.join(here, "..", "..", ".."))
out  = sys.argv[1]

def split_imports(txt):
  imps, body = [], []
  for line in txt.split("\n"):
    if line.startswith("import "):
      imps.append(line.split()[1])
    else:
      body.append(line)
  return imps, "\n".join(body)

twin = open(os.path.join(repo, "FAM/twin-primes/twin_primes_mathlib.lean")).read()
main = open(os.path.join(repo, "OEIS/A187011/A187011_mathlib.lean")).read()
grow = open(os.path.join(here, "Growth.lean.part")).read()
head = open(os.path.join(here, "header.lean.part")).read()

timps, tbody = split_imports(twin)
mimps, mbody = split_imports(main)

# Drop the leading /- ... -/ header of the A187011 file (it describes that
# file alone); keep everything after it.
#
mbody = mbody.lstrip()
if mbody.startswith("/-"):
  mbody = mbody[mbody.index("-/") + 2:]

imports = []
for m in timps + mimps:
  if m not in imports:
    imports.append(m)

with open(out, "w") as fp:
  fp.write("\n".join("import " + m for m in imports) + "\n\n")
  fp.write(head.rstrip() + "\n\n")
  fp.write("-- ===== FAM/twin-primes/twin_primes_mathlib.lean =====\n")
  fp.write(tbody.strip() + "\n\n")
  fp.write("-- ===== OEIS/A187011/A187011_mathlib.lean =====\n")
  fp.write(mbody.strip() + "\n\n")
  fp.write("-- ===== OEIS/A187011/certificate/Growth.lean.part =====\n")
  fp.write(grow.strip() + "\n")
