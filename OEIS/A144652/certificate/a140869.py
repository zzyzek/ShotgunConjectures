# A140869 / A144652: h not in the triangle => 4h+5 (resp. 4h+1) prime, h <= 10^5.
#
from sympy import isprime
H = 10**5
for name, off, c in (("A140869", -2, 5), ("A144652", 0, 1)):
  S = set()
  m = 1
  while (2*m + m + 1 + off) // 2 <= H:
    for n in range(1, m + 1):
      t = (2*m*n + m + n + off) // 2
      if t > H: break
      S.add(t)
    m += 1
  bad = [h for h in range(0, H + 1) if h not in S and not isprime(4*h + c)]
  print(name, "h <= 10^5 not in triangle with 4h+%d not prime:" % c, bad[:5])
