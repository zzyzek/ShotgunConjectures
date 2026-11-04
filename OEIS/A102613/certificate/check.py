# A102613: pi(n)/(n - pi(n)) for a few n (tends to 0 since pi(n)/n -> 0).
from sympy import primepi
print([(10**k, float(primepi(10**k)) / (10**k - int(primepi(10**k)))) for k in range(1, 10)])
