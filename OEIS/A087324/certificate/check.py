# A087324: n and its 9's complement 10^d - 1 - n (d = digits of n) with the same
# prime signature.  Since 10^d - 1 == 3 (mod 4) for d >= 2, n and its complement
# are never both squares, so no term has an all-even signature (p^2, p^2 q^2, ...).
# Lists terms < 10^5 and confirms none is a perfect square.
#
from math import isqrt
def sig(m):
  e = []; p = 2
  while p * p <= m:
    k = 0
    while m % p == 0: m //= p; k += 1
    if k: e.append(k)
    p += 1
  if m > 1: e.append(1)
  return sorted(e)
terms = [n for n in range(1, 10**5) if 10**len(str(n)) - 1 - n > 0 and sig(n) == sig(10**len(str(n)) - 1 - n)]
print("first terms:", terms[:20])
print("any square term:", [n for n in terms if isqrt(n)**2 == n])
