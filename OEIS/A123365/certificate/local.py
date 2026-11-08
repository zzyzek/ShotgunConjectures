# For B = q^a r^b (case A, K = 3) check the 2-adic and 3-adic conditions on m = 2(B-1)/(B-c(B)):
# m odd and 3 | m (m = p + 2, p = 1 mod 6). Count configs passing each.
from sympy import primerange
def cpe(q, e):
  return 1 + (q - 1)*sum(q**(e - 3*i - 1) for i in range((e - 1)//3 + 1))
def v(n, l):
  k = 0
  while n % l == 0: n //= l; k += 1
  return k
ps = [q for q in primerange(2, 300) if q % 3 == 2]
tot = ok2 = ok3 = ok23 = 0
from collections import Counter
cnt = Counter()
for i, q in enumerate(ps):
  for r in ps[i+1:]:
    for a in range(1, 13):
      if q > 2 and a % 3 == 1: continue
      for b in range(2, 13):
        if b % 3 == 1: continue
        B = q**a * r**b; C = cpe(q, a)*cpe(r, b); D = B - C; N2 = 2*(B - 1)
        if B % 3 != 1: continue
        tot += 1
        c2 = (v(D, 2) == v(N2, 2)); c3 = (v(D, 3) < v(N2, 3))
        ok2 += c2; ok3 += c3; ok23 += (c2 and c3)
        if c2 and c3: cnt[(q == 2, a % 3, b % 3)] += 1
print(tot, ok2, ok3, ok23); print(cnt)
