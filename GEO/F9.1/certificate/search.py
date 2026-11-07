# Local search for n points maximizing # unit circles through >= 3 of them.
import cmath, math, random, sys, itertools
def circles(P, tol=1e-7):
    cand = {}
    n = len(P)
    for i in range(n):
        for j in range(i+1, n):
            a, b = P[i], P[j]
            d = abs(b - a)
            if d < 1e-9 or d > 2 - 1e-12: continue
            m = (a + b) / 2; h = math.sqrt(max(0.0, 1 - d*d/4))
            w = (b - a) / d * 1j
            for c in (m + h*w, m - h*w):
                key = (round(c.real/tol), round(c.imag/tol))
                cand.setdefault(key, (c, set()))[1].update((i, j))
    # merge near keys via rounding at coarser level
    cnt = 0; seen = {}
    for key, (c, s) in cand.items():
        k2 = (round(c.real*1e5), round(c.imag*1e5))
        if k2 in seen: seen[k2] |= s
        else: seen[k2] = set(s)
    return sum(1 for s in seen.values() if len(s) >= 3)
w = cmath.exp(2j*math.pi/3)
def pool(rots, R=2):
    base = [a + b*w for a in range(-R, R+1) for b in range(-R, R+1) if abs(a + b*w) <= R + 1e-9]
    pts = set()
    for z1 in base:
        for r in rots:
            for z2 in base:
                p = z1 + r*z2
                if abs(p) <= 2.6: pts.add((round(p.real, 9), round(p.imag, 9)))
    return [complex(x, y) for x, y in pts]
def climb(pl, n, iters, seed):
    rnd = random.Random(seed)
    S = rnd.sample(range(len(pl)), n); best = circles([pl[i] for i in S])
    for it in range(iters):
        T = S[:]; T[rnd.randrange(n)] = rnd.randrange(len(pl))
        if len(set(T)) < n: continue
        v = circles([pl[i] for i in T])
        if v >= best: S, best = T, v
    return best, [pl[i] for i in S]
if __name__ == "__main__":
    n = int(sys.argv[1]); seeds = int(sys.argv[2]); iters = int(sys.argv[3])
    cm = 5/6; rho = complex(cm, math.sqrt(1 - cm*cm))
    cm2 = 7/8; rho2 = complex(cm2, math.sqrt(1 - cm2*cm2))
    th = 0.9137; rho3 = cmath.exp(1j*th)
    for name, rots in (("eis", [0]), ("moser", [0, rho]), ("78", [0, rho2]), ("gen", [0, rho3])):
        pl = pool(rots, 1 if len(rots) > 1 else 3)
        bb = 0; bp = None
        for s in range(seeds):
            b, P = climb(pl, n, iters, s)
            if b > bb: bb, bp = b, P
        print(name, len(pl), bb, [complex(round(z.real, 6), round(z.imag, 6)) for z in bp], flush=True)
