#!/usr/bin/env python3
# Assemble A215462_conj2_mathlib.lean: the FAM/twin-primes Lean file (which
# inlines the PrimeNumberTheoremAnd Selberg sieve, Apache 2.0, Arend
# Mellendijk, copyright headers kept) followed by our Goldbach / A215462
# part (Gold.lean.part). Imports of both parts are hoisted to the top;
# header.lean.part goes right after them.
#
# Usage: assemble.py <out.lean>   (run from anywhere)
#
import os, sys

here = os.path.dirname(os.path.abspath(__file__))
repo = os.path.normpath(os.path.join(here, "..", "..", ".."))
twin = open(os.path.join(repo, "FAM/twin-primes/twin_primes_mathlib.lean")).read()
part = open(os.path.join(here, "Gold.lean.part")).read()
header = open(os.path.join(here, "header.lean.part")).read()

imports, bodies = [], []
for txt in (twin, part):
  body = []
  for line in txt.split("\n"):
    if line.startswith("import "):
      if line.split()[1] not in imports:
        imports.append(line.split()[1])
      continue
    body.append(line)
  bodies.append("\n".join(body).strip("\n"))

with open(sys.argv[1], "w") as fp:
  fp.write("\n".join("import " + m for m in imports) + "\n\n")
  fp.write(header.strip("\n") + "\n\n")
  fp.write(bodies[0] + "\n\n")
  fp.write(bodies[1] + "\n")
