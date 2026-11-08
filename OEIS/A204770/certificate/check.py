# a(n): coefficients of prod (1-x^k)(1-x^(6k))/(1-x^(6k-3)); compare with the theta form
# a(n) = sum over k in Z, j >= 0 with k(3k-1)/2 + 3j(j+1)/2 = n of (-1)^k,
# i.e. 24n + 10 = (6k-1)^2 + 9(2j+1)^2.
import math
N = 20000
c = [0] * (N + 1); c[0] = 1
def mul(c, e, s):  # multiply by (1 + s x^e) truncated
    for i in range(N, e - 1, -1): c[i] += s * c[i - e]
for k in range(1, N + 1):
    mul(c, k, -1)
    if 6 * k <= N: mul(c, 6 * k, -1)
for k in range(1, N // 6 + 2):
    e = 6 * k - 3
    if e > N: break
    for i in range(e, N + 1): c[i] += c[i - e]   # divide by (1 - x^e)
t = [0] * (N + 1)
K = int(math.isqrt(2 * N)) + 3
for k in range(-K, K + 1):
    p = k * (3 * k - 1) // 2
    if p > N: continue
    j = 0
    while p + 3 * j * (j + 1) // 2 <= N:
        t[p + 3 * j * (j + 1) // 2] += (-1) ** (k % 2); j += 1
data = [1,-1,-1,1,-1,0,0,1,1,1,0,-1,-1,0,1,-2,1,0,0,-1,-1,-1,1,1,-1,2,1,0,0,1]
print('product == theta:', c == t, ' data ok:', c[:30] == data)
def s2(m):
    m2 = m
    q = 2
    while q * q <= m2:
        if m2 % q == 0:
            e = 0
            while m2 % q == 0: m2 //= q; e += 1
            if q % 4 == 3 and e % 2: return False
        q += 1
    return not (m2 > 1 and m2 % 4 == 3)
bad = [n for n in range(N + 1) if c[n] != 0 and not s2(24 * n + 10)]
print('nonzero but 24n+10 not a sum of two squares:', bad[:5])
for M in (100, 1000, 5000, 20000):
    print(M, 'fraction nonzero', sum(1 for n in range(M) if c[n]) / M, 'fraction 24n+10 in S2', sum(1 for n in range(M) if s2(24*n+10)) / M)
