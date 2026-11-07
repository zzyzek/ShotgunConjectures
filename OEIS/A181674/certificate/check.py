# A181674: a(n) = #{(P, m): P primorial (1 included), m semiprime, P + m = n}.
# Checks the data terms, then prints the mean (1/x) sum_{n<=x} a(n)
# = (1/x) sum_{P<=x} S(x-P), S = semiprime counting function, together with
# K(x) S(x) / x (K = number of primorials <= x), the upper bound used in the
# proof.  Both tend to 1 (slowly); loglog x is printed for comparison.
import numpy as np, math
N = 10**7
Om = np.zeros(N + 1, dtype=np.int8)
isp = np.ones(N + 1, dtype=bool); isp[:2] = False
for p in range(2, int(N ** 0.5) + 1):
    if isp[p]: isp[p * p::p] = False
for p in np.nonzero(isp)[0]:
    q = int(p)
    while q <= N:
        Om[q::q] += 1
        q *= int(p)
semi = (Om == 2)
S = np.cumsum(semi)
prim = [1]; 
for p in np.nonzero(isp)[0]:
    if prim[-1] * int(p) > N: break
    prim.append(prim[-1] * int(p))
def a(n): return sum(1 for P in prim if P < n and semi[n - P])
data = [0,0,0,0,1,1,1,1,0,2,2,2,0,0,2,3,1,0,0,1,1,1,2,1,0,1,3,2,0,0,1,1,0,2,2,3,1,0,3,4,2,0,0,2,2,0,1,1,0,1,2,3,1,0,2,2,2,1,2,1,1,0,3,3,1,1,1,2,1,1,2,0,0,0,2,2,0,1,2,1,1,0,2,1,1,1,3,4,1,0,1,3,2,1,3,2,2,0,2,1,1,0,0,1,0]
assert [a(n) for n in range(1, len(data) + 1)] == data
for e in range(3, 8):
    x = 10 ** e
    tot = sum(int(S[x - P]) for P in prim if P <= x)
    K = sum(1 for P in prim if P <= x)
    print("x=1e%d mean=%.4f  K*S(x)/x=%.4f  loglog x=%.3f" % (e, tot / x, K * int(S[x]) / x, math.log(math.log(x))))
