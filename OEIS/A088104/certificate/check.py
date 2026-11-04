# A088104: smallest n-digit prime beginning with prime(n).  Direct search n <= 14,
# and the inequality prime(n) < 25 ln^2(10^(n-1)) used with Dusart (2010) for n >= 7
# (checked for n <= 10^5; beyond, prime(n) < n(ln n + ln ln n) < 132 (n-1)^2).
#
from math import log
def isprime(n):
  if n < 2: return False
  for p in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41):
    if n % p == 0: return n == p
  d, s = n - 1, 0
  while d % 2 == 0: d //= 2; s += 1
  for a in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41):
    x = pow(a, d, n)
    if x in (1, n - 1): continue
    for _ in range(s - 1):
      x = x * x % n
      if x == n - 1: break
    else: return False
  return True
pr = [p for p in range(2, 1400000) if isprime(p)]
res = {}
for n in range(1, 15):
  P = pr[n - 1]; L = len(str(P))
  x = P * 10**(n - L)
  res[n] = next((v for v in range(x, x + 10**(n - L)) if isprime(v)), 0)
print(res)
print("prime(n) < 25 ln^2(10^(n-1)) for 2 <= n <= 10^5:", all(pr[n-1] < 25 * ((n - 1) * log(10))**2 for n in range(2, 100001)))
