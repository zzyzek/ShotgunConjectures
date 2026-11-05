#!/usr/bin/env python3
# Emit the Lean factor list of 2^3510 - 1 and a Pratt certificate for every prime
# factor not listed in UNCERT (primes whose p - 1 is not fully factored; their primality
# stays a hypothesis of the Lean theorems).
# p - 1 is factored by PARI/GP (`gp`), after dividing out the primes in data/hints.txt
# (found by ECM, ecm_stage1.gp); every step is re-checked by the Lean kernel.
# Usage: gen_factors3510.py <tools dir> data/factor3510.out [UNCERT ...]
#
import sys, subprocess
sys.path.insert(0, sys.argv[1])
import pratt_cert
from pratt_cert import steps, lean_list

hints = [int(l) for l in open("data/hints.txt") if l.strip()]

def gp_factor(n):
  out = subprocess.run(["gp", "-q", "-D", "parisize=100000000", "-D", "nbthreads=1"],
                       input="default(factor_proven, 1); f = factor(%d); for(i = 1, #f~, print(f[i,1], \" \", f[i,2]))\n" % n,
                       capture_output=True, text=True, timeout=250).stdout
  return {int(a): int(b) for a, b in (l.split() for l in out.split("\n") if l.strip())}

def factorint(n):
  fs = {}
  for h in hints:
    while n % h == 0:
      fs[h] = fs.get(h, 0) + 1
      n //= h
  for q, e in gp_factor(n).items() if n > 1 else []:
    fs[q] = fs.get(q, 0) + e
  return fs

pratt_cert.factorint = factorint

fs = [tuple(map(int, l.split())) for l in open(sys.argv[2]) if l.strip()]
fs.sort()
N  = 1
for p, e in fs:
  N *= p ** e
assert N == (2 ** 3510) - 1
uncert = [int(x) for x in sys.argv[3:]]
cert   = steps([p for p, _ in fs if p not in uncert])
print("def fs3510 : List (ℕ × ℕ) :=\n  [" + ",\n   ".join("(%d, %d)" % pe for pe in fs) + "]\n")
print("def cert3510 : List PrattStep :=\n  " + lean_list(cert, "   ") + "\n")
print("-- UNCERT " + " ".join(map(str, uncert)))
