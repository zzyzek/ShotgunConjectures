# Exact check in K = Q(sqrt3, sqrt11): elements as 4-tuples over basis 1, s3, s11, s33.
from fractions import Fraction as Fr
import itertools, math, sys
def K(a=0, b=0, c=0, d=0): return (Fr(a), Fr(b), Fr(c), Fr(d))
def add(x, y): return tuple(a + b for a, b in zip(x, y))
def neg(x): return tuple(-a for a in x)
def sub(x, y): return add(x, neg(y))
def mul(x, y):
    a1, b1, c1, d1 = x; a2, b2, c2, d2 = y
    # s3*s3=3, s11*s11=11, s3*s11=s33, s3*s33=3 s11, s11*s33=11 s3, s33*s33=33
    return (a1*a2 + 3*b1*b2 + 11*c1*c2 + 33*d1*d2,
            a1*b2 + b1*a2 + 11*c1*d2 + 11*d1*c2,
            a1*c2 + c1*a2 + 3*b1*d2 + 3*d1*b2,
            a1*d2 + d1*a2 + b1*c2 + c1*b2)
def conj3(x): return (x[0], -x[1], x[2], -x[3])
def conj11(x): return (x[0], x[1], -x[2], -x[3])
def inv(x):
    # x * conj3(x) lies in Q(s11); then times its conj11 lies in Q
    y = mul(x, conj3(x)); z = mul(y, conj11(y))
    assert z[1] == z[2] == z[3] == 0 and z[0] != 0
    return tuple(t / z[0] for t in mul(conj3(x), conj11(y)))
def val(x): return float(x[0] + x[1]*math.sqrt(3) + x[2]*math.sqrt(11) + x[3]*math.sqrt(33))
ONE = K(1); ZERO = K()
W = (K(Fr(-1, 2)), K(0, Fr(1, 2)))
RHO = (K(Fr(5, 6)), K(0, 0, Fr(1, 6)))
def cmul(p, q): return (sub(mul(p[0], q[0]), mul(p[1], q[1])), add(mul(p[0], q[1]), mul(p[1], q[0])))
def cadd(p, q): return (add(p[0], q[0]), add(p[1], q[1]))
def eis(a, b): return cadd((K(a), ZERO), cmul((K(b), ZERO), W))
def d2(p, q):
    dx, dy = sub(p[0], q[0]), sub(p[1], q[1]); return add(mul(dx, dx), mul(dy, dy))
def pool(R=1):
    base = [(a, b) for a in range(-R, R+1) for b in range(-R, R+1)]
    out = {}
    for (a1, b1) in base:
        for r in (0, 1):
            for (a2, b2) in base:
                p = eis(a1, b1)
                if r: p = cadd(p, cmul(eis(a2, b2), RHO))
                out[(round(val(p[0]), 5), round(val(p[1]), 5))] = p
    return out
def centre(p1, p2, p3):
    # solve 2(p2-p1).c = |p2|^2-|p1|^2, 2(p3-p1).c = |p3|^2-|p1|^2
    a11, a12 = sub(p2[0], p1[0]), sub(p2[1], p1[1])
    a21, a22 = sub(p3[0], p1[0]), sub(p3[1], p1[1])
    n = lambda p: add(mul(p[0], p[0]), mul(p[1], p[1]))
    r1 = mul(K(Fr(1, 2)), sub(n(p2), n(p1))); r2 = mul(K(Fr(1, 2)), sub(n(p3), n(p1)))
    det = sub(mul(a11, a22), mul(a12, a21))
    if det == ZERO: return None
    di = inv(det)
    return (mul(sub(mul(r1, a22), mul(a12, r2)), di), mul(sub(mul(a11, r2), mul(r1, a21)), di))
def count(P):
    cs = {}
    for i, j, k in itertools.combinations(range(len(P)), 3):
        c = centre(P[i], P[j], P[k])
        if c is None or d2(c, P[i]) != ONE: continue
        cs.setdefault(c, set()).update((i, j, k))
    return cs
if __name__ == "__main__":
    pl = pool(1)
    pts = eval(sys.argv[1])
    P = [pl[(round(z.real, 5), round(z.imag, 5))] for z in pts]
    assert len(set(P)) == len(P)
    cs = count(P)
    print(len(P), "points;", len(cs), "exact unit circles through >=3 points")
    for c, s in cs.items(): print(round(val(c[0]), 5), round(val(c[1]), 5), sorted(s))
