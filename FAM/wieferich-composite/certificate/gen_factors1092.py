#!/usr/bin/env python3
# Emit the Lean factor list and Pratt certificate for 2^1092 - 1 from
# factor1092.out (lines "p e", produced by factor1092.gp).
#
import sys
sys.path.insert(0, sys.argv[1])
from pratt_cert import steps, lean_list

fs = [tuple(map(int, l.split())) for l in open(sys.argv[2]) if l.strip()]
N  = 1
for p, e in fs:
  N *= p ** e
assert N == (2 ** 1092) - 1
cert = steps([p for p, _ in fs])
print("def fs1092 : List (ℕ × ℕ) :=\n  [" + ",\n   ".join("(%d, %d)" % pe for pe in fs) + "]\n")
print("def cert1092 : List PrattStep :=\n  " + lean_list(cert, "   ") + "\n")
