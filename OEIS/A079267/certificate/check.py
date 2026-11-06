# A079267: rows from Mathar's recurrence T(n+1,k) = T(n,k-1) + (2n-k) T(n,k) + (k+1) T(n,k+1);
# checks the factorial-moment identity sum_s C(s,k) T(n,s) = C(2n-k,k) (2n-2k-1)!!
# for n <= 80, and prints the total-variation distance of row n to Poisson(1).
from math import comb, factorial, exp
from fractions import Fraction
def odf(m):
    r = 1
    for i in range(m): r *= 2*i+1
    return r
rows = [[1]]
for n in range(0, 80):
    T = rows[-1] + [0, 0]
    rows.append([(T[k-1] if k else 0) + (2*n-k)*T[k] + (k+1)*T[k+1] for k in range(n+2)])
for n, r in enumerate(rows):
    assert sum(r) == odf(n)
    for k in range(n+1):
        assert sum(comb(s, k)*r[s] for s in range(n+1)) == comb(2*n-k, k)*odf(n-k), (n, k)
for n in (5, 10, 20, 40, 80):
    tv = sum(abs(r/odf(n) - exp(-1)/factorial(s)) for s, r in enumerate(rows[n])) / 2
    print(n, "TV distance to Poisson(1) ~", float(tv))
print("ok")
