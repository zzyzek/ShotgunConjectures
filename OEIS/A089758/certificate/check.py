# A089757 / A089758: greedy chain; each step prepends the least multiple of 3
# greater than the previous term that keeps the concatenation prime.  Builds 40 steps
# and checks gcd(C, 30) = 1 for every prime concatenation C (the Dirichlet hypothesis).
#
from sympy import isprime
from math import gcd
C, last, terms = 1, 0, []
for step in range(40):
  y = last + 3
  while not isprime(int(str(y) + str(C))): y += 3
  last, C = y, int(str(y) + str(C)); terms.append(y)
  assert gcd(C, 30) == 1
print(terms[:20])
