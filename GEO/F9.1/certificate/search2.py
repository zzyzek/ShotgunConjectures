import sys, math, cmath
sys.path.insert(0, '.')
from search import pool, climb, w
n = int(sys.argv[1]); seeds = int(sys.argv[2]); iters = int(sys.argv[3]); R = int(sys.argv[4])
cm = 5/6; rho = complex(cm, math.sqrt(1 - cm*cm))
pl = pool([0, rho], R)
res = []
for s in range(seeds):
    b, P = climb(pl, n, iters, 100 + s)
    res.append(b)
    print(s, b, [complex(round(z.real, 6), round(z.imag, 6)) for z in P] if b >= max(res) else "", flush=True)
print("max", max(res), "pool", len(pl))
