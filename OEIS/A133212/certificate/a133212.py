# A133212 vs 2*A038503(n+3), A038503(m) = sum_k C(m, 4k).
#
from math import comb
a = [1, 4, 12, 32]
while len(a) < 300: a.append(4*a[-1] - 6*a[-2] + 4*a[-3])
b = lambda m: sum(comb(m, 4*k) for k in range(m//4 + 1))
print("a(n) = 2*A038503(n+3) for 1 <= n < 300:", all(a[n] == 2*b(n+3) for n in range(1, 300)), " n=0:", a[0], 2*b(3))
