# A225919: f(k) = 1/(k+4), a(1) = 1, a(n) = least k with f(a(n-1)+1)+...+f(k) > f(a(n-2)+1)+...+f(a(n-1)).
# Claim: a(n) = r(n) for all n >= 1, where r(1..4) = 1, 11, 40, 124 and
# r(n) = 4r(n-1) - 4r(n-2) + 3r(n-3) - 2r(n-4).
#
# Write F(k) = H_{k+4}, x_n = r(n) + 9/2.  DeTemple (Amer. Math. Monthly 100 (1993) 468-470):
#   1/(24(m+1)^2) < H_m - ln(m + 1/2) - gamma < 1/(24 m^2)   (m >= 1).
# With Q_n = x_n x_{n-2} - x_{n-1}^2 and P_n = x_{n-2} - Q_n, ln(1+u) >= u/(1+u), ln(1-v) <= -v:
#   (S1) Q_n > 0 and Q_n/(x_n x_{n-2}) > 1/(12 (r(n-1)+4)^2)      =>  F(r(n)) - F(r(n-1)) > F(r(n-1)) - F(r(n-2))
#   (S2) P_n > 0 and P_n/x_{n-1}^2 >= 1/(24 (r(n)+3)^2) + 1/(24 (r(n-2)+4)^2)
#                                                                  =>  F(r(n)-1) - F(r(n-1)) <= F(r(n-1)) - F(r(n-2))
# so the greedy rule picks r(n) (n >= 3).  a(2) = 11 is the entry's base step (compare with 1).
# Part A: (S1), (S2) exactly (fractions) for 3 <= n <= N.
# Part B: tail n > N.  u_n = r(n) + 13/3 satisfies u_n = 3u_{n-1} - u_{n-2} + 2u_{n-3}
#   (char. poly (x - R)(x^2 - (3-R)x + 2/R), R = 2.8933 the real root of x^3 - 3x^2 + x - 2).
#   w_n = u_n - R u_{n-1} satisfies w_n = (3-R) w_{n-1} - (2/R) w_{n-2}; with lam a complex root of
#   x^2 - (3-R)x + 2/R, z_n = w_n - conj(lam) w_{n-1} = lam z_{n-1}, |z_n|^2 = w_n^2 - (3-R) w_n w_{n-1} + (2/R) w_{n-1}^2,
#   and |w_{n-1}| <= |z_n| / Im(lam).  Exactly, e_n = x_n - x_{n-1}^2/x_{n-2}
#   = (R-1)^2/6 + w_n - R w_{n-1} - (w_{n-1} - b)^2/x_{n-2},  b = (R-1)/6.
#   We bound |w| for n >= N by interval arithmetic and get 0.3 <= e_n <= 0.9, x_n <= 3 x_{n-1}, x_{n-2} >= 30,
#   which imply (S1) and (S2) (README).
from fractions import Fraction as Fr
from mpmath import iv, mp
import sys
N = 60
r = [None, 1, 11, 40, 124]
while len(r) <= N + 2:
    m = len(r)
    r.append(4*r[m-1] - 4*r[m-2] + 3*r[m-3] - 2*r[m-4])
data = [1,11,40,124,367,1070,3104,8989,26016,75280,217815,630210,1823388,5275597,15263836,
        44162700,127775471,369691398,1069624136,3094731965,8953954568,25906380024,74954649447,
        216865477466,627454543012,1815407450477,5252498763364,15196997925652]
assert r[1:len(data)+1] == data
# base step a(2) = 11: 1/6 + ... + 1/14 <= 1 < 1/6 + ... + 1/15
assert sum(Fr(1, j + 4) for j in range(2, 11)) <= 1 < sum(Fr(1, j + 4) for j in range(2, 12))
x = lambda n: Fr(r[n]) + Fr(9, 2)
for n in range(3, N + 1):
    Q = x(n)*x(n-2) - x(n-1)**2
    P = x(n-2) - Q
    assert Q > 0 and Q / (x(n)*x(n-2)) > Fr(1, 12*(r[n-1]+4)**2), n
    assert P > 0 and P / x(n-1)**2 >= Fr(1, 24*(r[n]+3)**2) + Fr(1, 24*(r[n-2]+4)**2), n
print("Part A ok for 3 <= n <=", N)
# u_n = r(n) + 13/3 satisfies the cubic recurrence (so the root-1 part of r is exactly -13/3)
for n in range(4, N + 3):
    assert Fr(r[n]) + Fr(13, 3) == 3*(Fr(r[n-1]) + Fr(13, 3)) - (Fr(r[n-2]) + Fr(13, 3)) + 2*(Fr(r[n-3]) + Fr(13, 3))
# Part B: isolate R by exact bisection on rationals.
p = lambda t: t**3 - 3*t**2 + t - 2
lo, hi = Fr(289, 100), Fr(29, 10)
assert p(lo) < 0 < p(hi)
for _ in range(400):
    mid = (lo + hi) / 2
    if p(mid) < 0: lo = mid
    else: hi = mid
iv.dps = 120
Ri = iv.mpf([lo, hi]) if False else iv.mpf([iv.mpf(lo.numerator)/lo.denominator, iv.mpf(hi.numerator)/hi.denominator])
Ri = iv.mpf([Ri.a, Ri.b])
u = lambda n: iv.mpf(r[n]) + iv.mpf(13)/3
w = lambda n: u(n) - Ri*u(n-1)
mod2 = 2/Ri
re = (3 - Ri)/2
im = iv.sqrt(mod2 - re**2)
wN, wN1 = w(N), w(N-1)
z2 = wN**2 - (3 - Ri)*wN*wN1 + mod2*wN1**2
zN = iv.sqrt(z2)
lam = iv.sqrt(mod2)
assert lam.b < 1
# |w_{n-1}| <= lam^(n-N) |z_N| / im for n >= N, so |w_m| <= W := |z_N|/im for all m >= N-1.
W = zN / im
b = (Ri - 1)/6
einf = (Ri - 1)**2/6
xmin = iv.mpf(r[N-2]) + iv.mpf(9)/2
dev = W + Ri*W + (W + b)**2 / xmin
# spot check of the exact formula for e_n
for n in (10, 30, N):
    en = x(n) - x(n-1)**2 / x(n-2)
    fe = einf + w(n) - Ri*w(n-1) - (w(n-1) - b)**2 / (iv.mpf(r[n-2]) + iv.mpf(9)/2)
    ei = iv.mpf(en.numerator) / en.denominator
    assert abs(ei - fe).b < 1e-50, n
print("e_inf in", mp.nstr(einf.a, 8), mp.nstr(einf.b, 8), " tail deviation <=", mp.nstr(dev.b, 8))
assert (einf - dev).a >= 0.3 and (einf + dev).b <= 0.9
# x_n <= 3 x_{n-1}: x_n = R x_{n-1} + w_n - b, and |w_n| <= W, R < 2.9, x_{n-1} >= 30
assert (Ri*1 + (W + b)/30).b < 3 and xmin.a >= 30
print("Part B ok: for n >", N, " 0.3 <= e_n <= 0.9")
