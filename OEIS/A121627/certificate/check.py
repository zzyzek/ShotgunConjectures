# A121627: a(n) = Re(prod_{k<=n} k(1+i)) = n! Re((1+i)^n).  Checks n <= 400:
# |a(n)| = n! 2^floor(n/2) when nonzero (n mod 8 not in {2,6}); each nonzero term divides
# the next nonzero term, and the quotient is divisible by the later index.
from math import factorial
z = complex(1, 0); a = []
re, im = 1, 1
A = [None, 1]
for n in range(2, 401):
  re, im = n * (re - im), n * (re + im); A.append(re)
nz = [n for n in range(1, 401) if A[n] != 0]
print("zeros exactly at n == 2, 6 mod 8:", all((A[n] == 0) == (n % 8 in (2, 6)) for n in range(1, 401)))
print("|a(n)| = n! 2^floor(n/2):", all(abs(A[n]) == factorial(n) * 2**(n // 2) for n in nz))
print("(1) and (2):", all(A[m] % A[n] == 0 and (A[m] // A[n]) % m == 0 for n, m in zip(nz, nz[1:])))
