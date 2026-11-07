# A119659 triangle claim: q_n = p_{p_n}; q_n + q_{n+1} > q_{n+2} for all n >= 4.
# (1) finite check for n <= NMAX; (2) the analytic inequality at m = 300 (it is increasing in m).
import numpy as np
from mpmath import mp, mpf, log
NMAX = 100000
LIM = 30000000
s = np.ones(LIM + 1, dtype=bool); s[:2] = False
for i in range(2, int(LIM ** 0.5) + 1):
    if s[i]: s[i*i::i] = False
P = np.nonzero(s)[0]
p = lambda k: int(P[k - 1])
q = [None] + [p(p(n)) for n in range(1, NMAX + 3)]
bad = [n for n in range(1, NMAX + 1) if q[n] + q[n + 1] <= q[n + 2]]
print("failing n <= %d:" % NMAX, bad, [(q[n], q[n+1], q[n+2]) for n in bad])
# p_n >= 300 iff n >= 63; all n <= 62 are covered by the finite check.
print("p_62, p_63 =", p(62), p(63))
mp.dps = 30
m = mpf(300)
lhs = 2 * m * log(m)
rhs = mpf('1.44') * m * (log(mpf('1.44') * m) + log(log(mpf('1.44') * m)))
print("2 m ln m - 1.44m(ln 1.44m + lnln 1.44m) at m = 300:", lhs - rhs)
# monotonicity: d/dm [0.56 ln m - 1.44 ln 1.44 + ... ] reduces to ln(1.44 m) > 1.44/0.56
print("ln(1.44*300) =", log(mpf('1.44') * 300), "> 1.44/0.56 =", mpf('1.44') / mpf('0.56'))
