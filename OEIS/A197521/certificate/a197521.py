# A197521: least x > 0 with cos(pi x/2) = cos(pi x/3)^2 versus 3 + t0,
# t0 = least t > 0 with sin(pi t/6) = sin(pi t/3)^2 (A197383); both from the
# cubic 4s^3 - 4s + 1 = 0, s = sin(pi t/6).
#
import mpmath as mp
mp.mp.dps = 50
f = lambda x: mp.cos(mp.pi*x/2) - mp.cos(mp.pi*x/3)**2
g = lambda t: mp.sin(mp.pi*t/6) - mp.sin(mp.pi*t/3)**2
s1 = min(r for r in mp.polyroots([4, 0, -4, 1]) if mp.im(r) == 0 and mp.re(r) > 0)
t0 = 6*mp.asin(s1)/mp.pi
print("t0 =", t0, " g(t0) =", g(t0), " f(3+t0) =", f(3 + t0))
xs = [mp.mpf(i)/1000 for i in range(1, 3521)]
print("sign changes of f on (0, 3.52]:", [x for a, x in zip(xs, xs[1:]) if f(a)*f(x) < 0][:5])
print("A197521 digits 3.52133782... :", mp.nstr(3 + t0, 30))
