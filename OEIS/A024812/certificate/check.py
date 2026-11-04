# A024812 / A024813: f(m) = floor(cot(pi/(2m))).  A024812 = positive values
# taken exactly once, A024813 = the m with f(m-1) < f(m) < f(m+1).
# Checks Jeffery's identity A024812(k) = (A024813(k) + k - 1)/2 for m < 2*10^5
# (mpmath, 40 digits; no f(m) lies within 1e-25 of an integer for m >= 3).
#
from mpmath import mp, cot, pi, floor, nint
mp.dps = 40
N = 200000
f = [None, 0] + [int(floor(cot(pi/(2*m)))) for m in range(2, N + 2)]
near = [m for m in range(3, N + 2) if abs(cot(pi/(2*m)) - nint(cot(pi/(2*m)))) < mp.mpf(10)**-25]
from collections import Counter
c = Counter(f[1:N + 1])
top = f[N]
once = [v for v in range(1, top) if c[v] == 1]
twice_max = max(c[v] for v in range(1, top))
A813 = [m for m in range(2, N + 1) if f[m-1] < f[m] < f[m+1]]
K = min(len(once), len(A813))
print("values taken 1 or 2 times only:", twice_max <= 2, " near-integers:", near[:5])
print("identity holds for k <=", K, ":", all(once[k-1] == (A813[k-1] + k - 1)//2 and (A813[k-1] + k - 1) % 2 == 0 for k in range(1, K + 1)))
