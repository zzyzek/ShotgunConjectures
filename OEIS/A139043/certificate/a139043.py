# A139043: S(x) = sum of primes <= x versus x^2/(2 log x - 1), x = 10^n,
# n <= 8 (sieve).  Ratio -> 1 (PNT) while the difference grows like
# x^2/(8 log^3 x) (li(x^2) expansion), so the "difference -> 0" reading fails.
#
import math
N = 10**8
sieve = bytearray([1]) * (N + 1)
sieve[0] = sieve[1] = 0
for i in range(2, int(N ** 0.5) + 1):
  if sieve[i]: sieve[i*i::i] = bytearray(len(range(i*i, N + 1, i)))
s, nxt, out = 0, 10, []
for i in range(N + 1):
  if sieve[i]: s += i
  if i == nxt:
    L = math.log(i)
    approx = i * i / (2 * L - 1)
    out.append((i, s, approx, s / approx, s - approx, i * i / (8 * L ** 3)))
    nxt *= 10
for row in out: print("x=%d S=%d approx=%.6g ratio=%.6f diff=%.4g x^2/(8 log^3 x)=%.4g" % row)
