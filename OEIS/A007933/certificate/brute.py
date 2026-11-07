from itertools import permutations
from sympy import isprime
def inA(n):
  return any(isprime(int(''.join(p))) for p in set(permutations(str(n))))
c=0
for n in range(1,10**5):
  if inA(n): c+=1
  if n+1 in (10,100,1000,10000,100000): print(n+1,c)
