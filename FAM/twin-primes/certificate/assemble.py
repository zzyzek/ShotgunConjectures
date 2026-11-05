#!/usr/bin/env python3
# Assemble Brun_mathlib.lean: the four Selberg-sieve files of
# PrimeNumberTheoremAnd (Apache 2.0, Arend Mellendijk), inlined because
# tools/leancheck-mathlib.sh checks a single file, followed by our own
# twin-prime application (src/Twin.lean.part).
#
# Edits to the copied files: imports hoisted to the top; a column-0
# `theorem`/`lemma` becomes `nonrec theorem`/`nonrec lemma`, so the check
# script prints axioms only for our own top-level theorems (which depend
# on all of the copied ones); each file's unclosed `noncomputable section`
# is closed. Copyright headers are kept (Apache 2.0).
#
# Usage: assemble.py <PrimeNumberTheoremAnd checkout> <out.lean>
#
import re, sys, os

pnt, out = sys.argv[1], sys.argv[2]
here = os.path.dirname(os.path.abspath(__file__))
sieve = os.path.join(pnt, "PrimeNumberTheoremAnd/Mathlib/NumberTheory/Sieve")
files = ["AuxResults", "Basic", "Selberg", "SelbergBounds"]

imports, bodies = [], []
for f in files:
  txt = open(os.path.join(sieve, f + ".lean")).read()
  body = []
  for line in txt.split("\n"):
    if line.startswith("import "):
      mod = line.split()[1]
      if (not mod.startswith("PrimeNumberTheoremAnd")) and (mod not in imports):
        imports.append(mod)
      continue
    line = re.sub(r"^theorem ", "nonrec theorem ", line)
    line = re.sub(r"^lemma ", "nonrec lemma ", line)
    body.append(line)
  body = "\n".join(body)
  closes = ( "" if f == "SelbergBounds" else "\nend\n" )
  bodies.append("-- ===== copied from PrimeNumberTheoremAnd " + f + ".lean =====\n" + body + closes)

part = open(os.path.join(here, "..", "src", "Twin.lean.part")).read()
pimports = [l.split()[1] for l in part.split("\n") if l.startswith("import ")]
for m in pimports:
  if m not in imports: imports.append(m)
part = "\n".join(l for l in part.split("\n") if not l.startswith("import "))
header = open(os.path.join(here, "..", "src", "header.lean.part")).read()

with open(out, "w") as fp:
  fp.write("\n".join("import " + m for m in imports) + "\n\n")
  fp.write(header + "\n")
  fp.write("\n".join(bodies) + "\n")
  fp.write(part)
