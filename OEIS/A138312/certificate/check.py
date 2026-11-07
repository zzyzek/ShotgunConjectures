# A138312/A138313: F(n) - H(n), F(n) = sum_{k<=n} mu^2(k)/phi(k), against
# B3 - gamma = sum_p log p/(p(p-1)) = 0.7553666108...  (numerical illustration;
# the identity itself is Ramare 1995 Lemma 3.4).
import math
N = 10**6
phi = list(range(N + 1)); sqf = [True] * (N + 1)
for p in range(2, N + 1):
    if phi[p] == p:
        for m in range(p, N + 1, p): phi[m] -= phi[m] // p
        for m in range(p * p, N + 1, p * p): sqf[m] = False
F = H = 0.0
for k in range(1, N + 1):
    H += 1.0 / k
    if sqf[k]: F += 1.0 / phi[k]
S = sum(math.log(p) / (p * (p - 1)) for p in range(2, N + 1) if phi[p] == p - 1)
print("F-H at 1e6 = %.6f ; partial sum_p log p/(p(p-1)) = %.9f ; A138312 = 0.755366610" % (F - H, S))
assert abs(S - 0.755366610) < 1e-5 and abs((F - H) - S) < 0.01
