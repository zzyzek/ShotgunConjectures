# A125148: for odd x not divisible by 5 there is a prime x + 10m (m >= 0).  x < 10^5.
from sympy import isprime
ok = True
for x in range(1, 10**5, 2):
  if x % 5 == 0: continue
  m = 0
  while not isprime(x + 10*m): m += 1
print("all found")
