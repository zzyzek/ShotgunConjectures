# A088120, n = 12: every value prod_{i<12}(a + i d) + d below W = 1*3*...*23 + 2
# is listed and tested; W is tested for primality (sympy isprime is a proof below 2^64).
#
from sympy import isprime, factorint
def f(n, a, d):
  r = d
  p = 1
  for i in range(n): p *= a + i*d
  return p + d
n, W = 12, f(12, 1, 2)
print("W =", W, "prime:", isprime(W))
d = 1
while f(n, 1, d) <= W:
  a = 1
  while f(n, a, d) <= W:
    v = f(n, a, d); print(" a=%d d=%d v=%d prime=%s factors=%s" % (a, d, v, isprime(v), factorint(v) if v != W else '-'))
    a += 1
  d += 1
