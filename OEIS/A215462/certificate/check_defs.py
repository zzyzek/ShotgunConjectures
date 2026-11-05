#!/usr/bin/env python3
# Compare the Lean definitions of A215462, A215461, A002372 (convolution form:
# pairs (2i+1, 2(n-1-i)+1), i < n) with the terms listed in the OEIS entries,
# check A002372 + A215461 + A215462 = n, and report the last n <= NMAX where
# conjecture 2 (A215461 < A215462 and A002372 < A215461) fails.
#
import sys

NMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 200000
M = 2 * NMAX + 2
sieve = bytearray([1]) * M
sieve[0] = sieve[1] = 0
for p in range(2, int(M ** 0.5) + 1):
  if sieve[p]:
    sieve[p * p::p] = bytearray(len(sieve[p * p::p]))

def terms(n):
  a = b = g = 0
  for i in range(n):
    l, r = sieve[2 * i + 1], sieve[2 * (n - 1 - i) + 1]
    if l and r:       g += 1
    elif l or r:      b += 1
    else:             a += 1
  return a, b, g

A215462 = [0,1,0,0,0,2,0,0,2,1,0,2,2,2,2,3,0,4,6,0,4,5,2,4,6,5,4,7,4,6]
A215461 = [0,0,2,2,2,0,4,4,2,4,6,4,4,6,8,6,12,6,4,16,10,8,14,12,8,12,16,10,18,16]
for n in range(30):
  a, b, g = terms(n)
  assert (a, b) == (A215462[n], A215461[n]), n
  assert a + b + g == n
print("first 30 terms of A215462, A215461 match; a + b + g = n")

# All n <= NMAX at once: g(n) = sum_i c(i) c(n-1-i) with c(i) = [2i+1 prime],
# an integer convolution (FFT, rounded); a, b from a + b + g = n and
# b = 2 (P(n) - g(n)), P(n) = #{i < n : 2i+1 prime}.
#
import numpy as np
c = np.array([sieve[2 * i + 1] for i in range(NMAX)], dtype=np.float64)
L = 1
while L < 2 * NMAX: L *= 2
conv = np.rint(np.fft.irfft(np.fft.rfft(c, L) ** 2, L)[:NMAX]).astype(np.int64)
P = np.concatenate(([0], np.cumsum(c).astype(np.int64)))
last = None
for n in range(1, NMAX + 1):
  g = int(conv[n - 1])
  b = 2 * (int(P[n]) - g)
  a = n - b - g
  if n < 3000: assert (a, b, g) == terms(n)
  if not (b < a and g < b): last = n
print("NMAX =", NMAX, " last n <= NMAX where conjecture 2 fails:", last)
