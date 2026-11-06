# Walk model of A054393 (Alcover's matrix power): levels 0,1,2,...; steps: up 1,
# drop to any lower level, loop only at levels 0..4. a(n) = closed walks 0 -> 0.
# Check: DP terms = OEIS data; A(x) = B(z), z = x*Motzkin(x), B = g.f. of A152718.
import sympy as sp
N = 40
def dp(N):
    w = [1] + [0]*N; out = [1]
    for n in range(N):
        nw = [0]*(N+1)
        for j in range(N+1):
            s = (w[j-1] if j > 0 else 0) + (w[j] if j <= 4 else 0) + sum(w[j+1:])
            nw[j] = s
        w = nw; out.append(w[0])
    return out
a = dp(N)
oeis = [1,1,2,5,14,42,132,428,1417,4757,16119,54963,188219,646460,2224944,7668915,26461005,91371594,315689675,1091166442,3772747245,13047503222,45131078409,156129312025,540181837728,1869097588540,6467740095295]
assert a[:len(oeis)] == oeis, "dp mismatch"
b = [1,1,1,1,2,4]
while len(b) <= N: b.append(2*b[-1]-b[-2]+2*b[-3]-b[-4]+b[-5])
# t(n,k) = [x^n] z^k, z = x(1+z+z^2)
t = [[0]*(N+2) for _ in range(N+1)]; t[0][0] = 1
for n in range(N):
    for k in range(1, N+1):
        t[n+1][k] = t[n][k-1] + t[n][k] + t[n][k+1]
c = [sum(b[k]*t[n][k] for k in range(n+1)) for n in range(N+1)]
print("transform == dp up to", N, ":", c == a)
# symbolic: E_h, S_h in terms of z
z = sp.symbols('z'); x = z/(1+z+z**2)
S = x*z; E = z/x   # level 4: S_4 = x z, E_4 = M = z/x
for h in [3,2,1,0]:
    S = sp.simplify(x*E*(1+S)); E = sp.simplify(1/(1-x-S))
B = 1 + z*(-1+z+z**3)/(-1+2*z-z**2+2*z**3-z**4+z**5)
print("E_0 - B(z) =", sp.simplify(E - B))
