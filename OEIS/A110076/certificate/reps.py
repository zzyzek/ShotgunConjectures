# Representations 10^n = prod sigma(p_i^e_i), distinct primes p_i = 2^a 5^b - 1 (BPSW list),
# e_i = 1 (vector (a,b)); also sigma(3^3) = 40 -> (3,1) and sigma(7^3) = 400 -> (4,2).
import sys
from itertools import combinations
Q = []
for l in open('qlist.out'):
    if l.startswith('rc'): continue
    a, b = map(int, l.split()); Q.append((a, b))
items = [((a, b), (a, b)) for (a, b) in Q]          # (prime id, vector)
items += [((2, 0), (3, 1)), ((3, 0), (4, 2))]
vec = {}
for pid, v in items: vec.setdefault(v, []).append(pid)
N = int(sys.argv[1])
pairsum = {}
for i in range(len(items)):
    for j in range(i + 1, len(items)):
        (p1, v1), (p2, v2) = items[i], items[j]
        if p1 == p2: continue
        s = (v1[0] + v2[0], v1[1] + v2[1])
        if s[0] <= N and s[1] <= N: pairsum.setdefault(s, []).append((i, j))
out = open('reps.out', 'w')
for n in range(4, N + 1):
    rep = None
    for (i, j) in pairsum.get((n, n), []):
        rep = [items[i], items[j]]; break
    if rep is None:
        for i, (p1, v1) in enumerate(items):
            r = (n - v1[0], n - v1[1])
            for (j, k) in pairsum.get(r, []):
                if p1 not in (items[j][0], items[k][0]): rep = [items[i], items[j], items[k]]; break
            if rep: break
    if rep is None:
        for s, lst in pairsum.items():
            r = (n - s[0], n - s[1])
            if r in pairsum:
                for (i, j) in lst:
                    for (k, l) in pairsum[r]:
                        ids = {items[i][0], items[j][0], items[k][0], items[l][0]}
                        if len(ids) == 4: rep = [items[i], items[j], items[k], items[l]]; break
                    if rep: break
            if rep: break
    out.write(f"{n} {len(rep) if rep else 0} {rep}\n")
    if rep is None: print('NONE', n, flush=True)
out.close()
