# Count "diagonals" in the two grids of OEIS A216196 under candidate readings.
G1 = """1 2 3 4 5 6 7 8 9
6 5 4 9 8 7 3 2 1
7 8 9 1 2 3 4 5 6
2 3 1 5 6 4 8 9 7
4 6 5 7 9 8 1 3 2
8 9 7 2 3 1 5 6 4
3 1 2 6 4 5 9 7 8
5 4 6 8 7 9 2 1 3
9 7 8 3 1 2 6 4 5"""
G2 = """1 8 3 4 2 6 7 5 9
6 5 4 9 8 7 3 2 1
7 2 9 1 5 3 4 8 6
2 9 1 5 3 4 8 6 7
4 6 5 7 9 8 1 3 2
8 3 7 2 6 1 5 9 4
3 7 2 6 1 5 9 4 8
5 4 6 8 7 9 2 1 3
9 1 8 3 4 2 6 7 5"""
from itertools import combinations
def parse(s): return [list(map(int, l.split())) for l in s.splitlines()]
def is_sudoku(g):
    ok = all(len(set(r)) == 9 for r in g) and all(len({g[i][j] for i in range(9)}) == 9 for j in range(9))
    return ok and all(len({g[3*a+i][3*b+j] for i in range(3) for j in range(3)}) == 9 for a in range(3) for b in range(3))
def xoox(g):
    return sum(1 for i, j in combinations(range(9), 2) for k, l in combinations(range(9), 2)
               if g[i][k] == g[j][l] and g[i][l] == g[j][k])
def diags(g, slope):
    return sum(1 for c in range(9) if len({g[r][(c + slope * r) % 9] for r in range(9)}) == 9)
for name, s in (("G1", G1), ("G2", G2)):
    g = parse(s)
    print(name, "sudoku", is_sudoku(g), "xoox", xoox(g), {k: diags(g, k) for k in range(1, 9)})
from collections import Counter
for name, s in (("G1", G1), ("G2", G2)):
    g = parse(s)
    h = {k: Counter(len({g[r][(c + k * r) % 9] for r in range(9)}) for c in range(9)) for k in (1, 8)}
    # 3-cell diagonals within boxes (wrapping inside the box), both directions
    box = Counter()
    for a in range(3):
        for b in range(3):
            for d in (1, 2):
                for c in range(3):
                    cells = [g[3*a + r][3*b + (c + d*r) % 3] for r in range(3)]
                    box[(d, len(set(cells)), sum(cells))] += 1
    # 3-cell segments of torus slope +-1 diagonals that are arithmetic / sum 15
    seg = sum(1 for k in (1, 8) for r0 in range(9) for c0 in range(9)
              if len({g[(r0 + t) % 9][(c0 + k*t) % 9] for t in range(3)}) == 3)
    # digit d lies on a common slope +-1 torus diagonal in all its 9 cells?
    same = sum(1 for k in (1, 8) for c in range(9) if len({g[r][(c + k*r) % 9] for r in range(9)}) == 1)
    print(name, h, "box", sorted(box.items())[:12], "seg3distinct", seg, "constdiag", same)
for name, s in (("G1", G1), ("G2", G2)):
    g = parse(s)
    cnt = {k: Counter(len({g[r][(c + k * r) % 9] for r in range(9)}) for c in range(9)) for k in range(1, 9)}
    tot3 = sum(cnt[k][3] for k in cnt); tot9 = sum(cnt[k][9] for k in cnt)
    # 3-cell segments (box-internal lines across all 9 boxes and the 3 offsets) that are the same digit set as other segments ...
    print(name, "lines with 3 distinct", tot3, "with 9 distinct", tot9, {k: dict(cnt[k]) for k in cnt})
props = {"mod3": lambda c: len({x % 3 for x in c}) == 3, "grp": lambda c: len({(x-1)//3 for x in c}) == 3, "s15": lambda c: sum(c) == 15}
for name, s in (("G1", G1), ("G2", G2)):
    g = parse(s); out = {}
    for pn, pf in props.items():
        inner = sum(1 for a in range(3) for b in range(3) for d in (1, 2) for c in range(3)
                    if pf([g[3*a + r][3*b + (c + d*r) % 3] for r in range(3)]))
        torus3 = sum(1 for k in (1, 8) for r0 in range(0, 9, 3) for c0 in range(9)
                    if pf([g[r0 + t][(c0 + k*t) % 9] for t in range(3)]))
        out[pn] = (inner, torus3)
    print(name, out)
print("---- AP / s15 counts on 3-cell diagonal segments")
def ap(c): return c[1] - c[0] == c[2] - c[1]
for name, s in (("G1", G1), ("G2", G2)):
    g = parse(s)
    res = {}
    for pn, pf in (("ap", ap), ("s15", lambda c: sum(c) == 15), ("ap1", lambda c: ap(c) and abs(c[1]-c[0]) == 1), ("ap4", lambda c: ap(c) and abs(c[1]-c[0]) == 4)):
        boxwrap = sum(1 for A in range(3) for B in range(3) for d in (1, 2) for c in range(3)
                      if pf([g[3*A + r][3*B + (c + d*r) % 3] for r in range(3)]))
        boxmain = sum(1 for A in range(3) for B in range(3) for d in (1, 2)
                      if pf([g[3*A + r][3*B + (r if d == 1 else 2 - r)] for r in range(3)]))
        torus = sum(1 for k in (1, 8) for r0 in range(9) for c0 in range(9)
                    if pf([g[(r0 + t) % 9][(c0 + k*t) % 9] for t in range(3)]))
        plane = sum(1 for k in (1, -1) for r0 in range(7) for c0 in range(9)
                    if 0 <= c0 + 2*k < 9 and pf([g[r0 + t][c0 + k*t] for t in range(3)]))
        res[pn] = (boxwrap, boxmain, torus, plane)
    print(name, res)
print("---- equal diagonal neighbours")
for name, s in (("G1", G1), ("G2", G2)):
    g = parse(s)
    tor = sum(1 for r in range(9) for c in range(9) for k in (1, -1) if g[r][c] == g[(r+1) % 9][(c+k) % 9])
    pl = sum(1 for r in range(8) for c in range(9) for k in (1, -1) if 0 <= c+k < 9 and g[r][c] == g[r+1][c+k])
    tor2 = sum(1 for r in range(9) for c in range(9) for k in (1, -1) for t in range(1, 9) if g[r][c] == g[(r+t) % 9][(c+k*t) % 9])
    print(name, "torus adj", tor, "plane adj", pl, "same digit on common torus diagonal (ordered pairs/2)", tor2 // 2)
