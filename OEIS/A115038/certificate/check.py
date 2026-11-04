# A115038: every prime p is y^k - x^2 with k >= 2: odd p = ((p+1)/2)^2 - ((p-1)/2)^2, 2 = 3^3 - 5^2.
from sympy import primerange
print(all(((p+1)//2)**2 - ((p-1)//2)**2 == p for p in primerange(3, 10**6)), 3**3 - 5**2 == 2)
