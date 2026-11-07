# Case B condition: ceil(h/2) >= floor(sqrt(4p-7)) + 1, h = floor((n-2)/2), p = prime(n).
# Find the last n <= 20000 where it fails; above 20000 use p_n < n(ln n + ln ln n) (Rosser-Schoenfeld, n >= 6).
from sympy import primerange
PR=list(primerange(2,300000))
prime=lambda n: PR[n-1]
from math import isqrt, log, sqrt, ceil
last=None
for n in range(4,20001):
    p=prime(n); h=(n-2)//2
    if not ( (h+1)//2 >= isqrt(4*p-7)+1 ): last=n
print("last failing n <= 20000:", last)
# analytic tail: f(n) = (h+1)//2 - (sqrt(4 n(ln n + ln ln n) - 7) + 1) >= (n-3)/4 - 2 sqrt(n(ln n+ln ln n)) - 1
g=lambda n: (n-3)/4 - 2*sqrt(n*(log(n)+log(log(n)))) - 1
print("g(20000)=",g(20000), "min over 20000..1e7 sample:", min(g(n) for n in range(20000,10**7,997)))
