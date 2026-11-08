# K = 3 case A of A123365: B = q^a r^b, q < r primes = 2 mod 3.
# Test whether D = B - c(B) divides 2(B - 1); report quotient p + 2 and near-misses.
import sys
from sympy import isprime, primerange
Q = int(sys.argv[1]); E = int(sys.argv[2])
def cpe(q, e):
  return 1 + (q - 1)*sum(q**(e - 3*i - 1) for i in range((e - 1)//3 + 1))
ps = [q for q in primerange(2, Q) if q % 3 == 2]
hits = []
for i, q in enumerate(ps):
  for r in ps[i+1:]:
    for a in range(1, E+1):
      ca = cpe(q, a); qa = q**a
      for b in range(1, E+1):
        B = qa*r**b; C = ca*cpe(r, b); D = B - C
        if D > 0 and (2*(B - 1)) % D == 0:
          hits.append((q, a, r, b, 2*(B-1)//D - 2))
print(len(hits)); print(hits[:50])
