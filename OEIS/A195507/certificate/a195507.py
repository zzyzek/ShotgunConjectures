# A195507: a(n) = least m > n with m = n mod k for k = 1..n-1, by brute force
# (n <= 14), equals n + lcm(1..n-1); the stated recurrence for n < 400.
#
from math import gcd
from functools import reduce
L = lambda n: reduce(lambda x, y: x*y//gcd(x, y), range(1, n), 1)
def brute(n):
  m = n + 1
  while any((m - n) % k for k in range(1, n)): m += 1
  return m
print("brute = n + lcm(1..n-1), n <= 14:", all(brute(n) == n + L(n) for n in range(1, 15)))
ok = True
for n in range(1, 400):
  a, b = n + L(n), n + 1 + L(n + 1)
  d = n // gcd(a, n)
  ok &= (b == d*a - (d - 1)*n + 1)
print("recurrence a(n+1) = d a(n) - (d-1) n + 1 for n < 400:", ok)
