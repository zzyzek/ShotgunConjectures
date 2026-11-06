# A209998: build v(n,x) by the entry's Mathematica recursion, compare rows with the OEIS data,
# and compare the penultimate term of row n with A199923(n-1) (gcd-sum definition).
from math import gcd
def rows(N):
    u = [1]; v = [1]; out = [v[:]]
    for n in range(2, N + 1):
        nu = [0] * n; nv = [0] * n
        for i, c in enumerate(u): nu[i + 1] += c; nv[i + 1] += c; nv[i] += c
        for i, c in enumerate(v): nu[i + 1] += 2 * c; nv[i + 1] += 2 * c
        nu[0] += 1; nv[0] += 1
        u, v = nu, nv; out.append(v[:])
    return out
def A199923(n):
    if n == 0: return 1
    q = 3 ** (n - 1); return sum(gcd(k, q) for k in range(q + 1))
R = rows(14)
data = [1,2,3,2,8,9,2,10,30,27,2,10,46,108,81,2,10,50,198,378,243,2,10,50,242,810,1296,729,2,10,50,250,1122,3186,4374,2187,2,10,50,250,1234,4986,12150,14580,6561,2,10,50,250,1250,5946,21330,45198,48114,19683]
flat = [c for r in R for c in r]
print('data match:', flat[:len(data)] == data)
for n in range(2, 12):
    print(n, 'penultimate', R[n - 1][-2], 'A199923(n-1)', A199923(n - 1), 'A199923(n)', A199923(n))
