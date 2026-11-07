# Counterexample to Forsgard-Shapiro Conjectures 8, 9, 10 (Shapiro, arXiv 1503.05295, Sec. 7).
# P(x) = (19x^2 - 94x + 163) * prod_{j=0}^{21} (2D x + 2D + 2j - 23),  D = 10^5.
# The quadratic factor is the cofactor of (x+1)^22 in the Katkova-Shapiro-Vishnyakova
# polynomial Q_24 (arXiv 2403.12200, Sec. 5), scaled to integers; the linear factors split
# the 22-fold root -1 into 22 distinct rational roots -1 - (2j-23)/(2D).
from fractions import Fraction as F
from math import comb
import sys
D = 10**5
def mul(p, q):
    r = [0]*(len(p)+len(q)-1)
    for i, a in enumerate(p):
        for j, b in enumerate(q):
            r[i+j] += a*b
    return r
P = [163, -94, 19]
for j in range(22):
    P = mul(P, [2*D + 2*j - 23, 2*D])
n = len(P) - 1
assert n == 24 and all(c > 0 for c in P)
for j in range(22):
    x = F(-(2*D + 2*j - 23), 2*D)
    assert sum(c * x**k for k, c in enumerate(P)) == 0
assert 94**2 - 4*19*163 < 0
w = [P[k]*comb(n, k) for k in range(n+1)]
verts = [j for j in range(n+1)
         if all(w[i]**(l-j) * w[l]**(j-i) < w[j]**(l-i)
                for i in range(j) for l in range(j+1, n+1))]
corners = len(verts) - 1
A = [0] + P + [0]
def v(tilde):
    ks = [k for k in range(n+1)
          if ((k+1)*A[k+1]**2 - k*A[k]*A[k+2] > 0 if tilde else A[k+1]**2 - A[k]*A[k+2] >= 0)]
    return sum(1 for i in range(1, len(ks)) if ks[i] % 2 != ks[i-1] % 2), ks
print("degree", n, "distinct real roots", 22, "(quadratic factor has no real roots)")
print("tropical corners", corners, "hull vertices", verts)
print("Conj 10: v =", *v(False))
print("Conj 9 : v~ =", *v(True))
