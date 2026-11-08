# Zeros of A097806^k * tau (binomial transform: sum_j C(k,j) tau(n-j)) and of
# the k-fold partial sums of tau, for 0 <= k <= K and 1 <= n <= N.
import sys
N, K = int(sys.argv[1]), int(sys.argv[2])
# tau(n) = coefficient of x^n in x * prod (1 - x^m)^24, via Euler pentagonal
# series cubed is slow; use prod (1-x^m)^24 = (prod(1-x^m))^24 with pentagonal p.
e = [0] * N
k = 0
while True:
    done = True
    for s in (1, -1):
        g = k * (3 * k - s) // 2 if k else 0
        if g < N:
            e[g] = (-1) ** k
            done = False
    if done and k: break
    k += 1
    if k > 2 * int(N ** 0.5) + 5: break
def mul(a, b):
    c = [0] * N
    for i, x in enumerate(a):
        if x:
            for j in range(N - i):
                if b[j]: c[i + j] += x * b[j]
    return c
p2 = mul(e, e); p4 = mul(p2, p2); p8 = mul(p4, p4); p16 = mul(p8, p8); p24 = mul(p16, p8)
tau = [0] + p24[:N - 1]
zb, zp = [], []
a = tau[:]; b = tau[:]
for k in range(K + 1):
    zb += [(k, n) for n in range(1, N) if a[n] == 0]
    zp += [(k, n) for n in range(1, N) if b[n] == 0]
    a = [a[n] + (a[n - 1] if n > 1 else 0) for n in range(N)]
    s = 0; nb = [0] * N
    for n in range(1, N): s += b[n]; nb[n] = s
    b = nb
print("N", N - 1, "K", K)
print("binomial-transform zeros (k, n):", zb[:40])
print("partial-sum zeros (k, n):", zp[:40])
