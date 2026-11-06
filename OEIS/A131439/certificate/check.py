# A131439 = inverse binomial transform (zero offset) of A131438(n) = (2+n)2^n - 2 - 3n.
# Checks the OEIS data, the closed form 1, 7, then 4n+2 (n >= 3), and that the
# inverse binomial transform of A131439 is 1, 6, then (-1)^m (3m-5).
from math import comb
N = 200
b = [(2 + (k + 1)) * 2 ** (k + 1) - 2 - 3 * (k + 1) for k in range(N)]
inv = lambda f, m: sum((-1) ** (m - k) * comb(m, k) * f[k] for k in range(m + 1))
c = [inv(b, m) for m in range(N)]
data = [1,7,14,18,22,26,30,34,38,42,46,50,54,58,62,66,70,74,78,82,86,90,94,
        98,102,106,110,114,118,122,126,130,134,138,142,146,150,154,158,162,
        166,170,174,178,182]
assert c[:len(data)] == data
assert c[0] == 1 and c[1] == 7 and all(c[m] == 4 * (m + 1) + 2 for m in range(2, N))
d = [inv(c, m) for m in range(N)]
assert d[:10] == [1, 6, 1, -4, 7, -10, 13, -16, 19, -22]
assert all(d[m] == (-1) ** m * (3 * m - 5) for m in range(2, N))
print("ok", N)
