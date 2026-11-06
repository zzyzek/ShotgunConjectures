#!/usr/bin/env python3
#
# Check the reading of OEIS A095380: a(n) = number of m <= 2^n that are
# not values of sigma (A007369).  Recomputes the printed terms n <= 17
# and prints a(n)/2^n.  This only confirms the reading; the limit
# a(n)/2^n -> 1 is Ford's theorem, not a computation.
#
# Run: nice -n 19 timeout 300 python3 check.py   (about 10 s)
#

PRINTED = [1,1,2,6,15,34,75,162,337,706,1466,2995,6119,12450,25248,51158,103450]

NMAX = 17
X    = 2**NMAX

# sigma(m) >= m, so every sigma value <= X comes from some m <= X.
#
sig = [0]*(X+1)
for d in range(1, X+1):
  for m in range(d, X+1, d):
    sig[m] += d
hit = bytearray(X+1)
for m in range(1, X+1):
  if sig[m] <= X: hit[sig[m]] = 1

a = []
for n in range(1, NMAX+1):
  x = 2**n
  a.append(x - sum(hit[1:x+1]))
print("a(1..17):", a)
print("matches printed:", a == PRINTED)
print("a(n)/2^n:", [round(v/2**(i+1), 4) for i, v in enumerate(a)])
print("ALL OK" if a == PRINTED else "FAILED")
