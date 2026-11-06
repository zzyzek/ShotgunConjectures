#!/usr/bin/env python3
#
# Check for OEIS A030210 = q (prod_{k>=1} (1-q^k)(1-q^{5k}))^4.
#
# 1. The q-expansion matches the printed terms and the LMFDB newform
#    5.4.a.a coefficients a(1..13) = 1,-4,2,8,-5,-8,6,0,-23,20,32,16,-38.
# 2. |a(p)| < 2 p^(3/2) for all primes p < 10^4, tested exactly as
#    a(p)^2 < 4 p^3; prints the largest ratio |a(p)| / (2 p^(3/2)).
# 3. a(5) = -5.
#
# Product computed from Euler's pentagonal series with numpy int64
# convolutions (all coefficients stay far below 2^63).
#
# Run: nice -n 19 timeout 300 python3 check.py   (a few seconds)
#

import numpy as np

N = 10000

PRINTED = [1,-4,2,8,-5,-8,6,0,-23,20,32,16,-38,-24,-10,-64,26,92,100,-40,12]
LMFDB   = [1,-4,2,8,-5,-8,6,0,-23,20,32,16,-38]

def euler(step):
  # prod_{k>=1} (1 - q^(step k)) up to q^N, pentagonal number theorem.
  #
  e = np.zeros(N+1, dtype=np.int64)
  j = 0
  while True:
    done = True
    for g in ( (j*(3*j-1))//2, (j*(3*j+1))//2 ):
      if ( (step*g <= N) ) :
        e[step*g] = ( 1 if (j % 2 == 0) else -1 )
        done = False
    if done: break
    j += 1
  return e

A = np.convolve(euler(1), euler(5))[:N+1]
B = np.convolve(A, A)[:N+1]
C = np.convolve(B, B)[:N+1]

# a(n) = coefficient of q^(n-1) in C.
#
a = lambda n: int(C[n-1])

ok = ( [a(n) for n in range(1, 22)] == PRINTED ) and ( [a(n) for n in range(1, 14)] == LMFDB )
print("printed terms and LMFDB 5.4.a.a match:", ok)

sieve = bytearray([1])*(N+1)
sieve[0] = sieve[1] = 0
for i in range(2, int(N**0.5)+1):
  if sieve[i]: sieve[i*i::i] = bytearray(len(sieve[i*i::i]))
primes = [ p for p in range(2, N+1) if sieve[p] ]

viol = [ p for p in primes if a(p)**2 >= 4*p**3 ]
worst = max(primes, key=lambda p: abs(a(p)) / (2*p**1.5))
print(f"primes < {N}: {len(primes)}, violations of a(p)^2 < 4p^3: {viol}")
print(f"largest |a(p)|/(2p^1.5): p={worst}, a(p)={a(worst)}, ratio={abs(a(worst))/(2*worst**1.5):.6f}")
print("a(5) =", a(5))
ok &= ( (not viol) and (a(5) == -5) )
print("ALL OK" if ok else "FAILED")
