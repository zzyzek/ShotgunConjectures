# CNF: 9x9 Sudoku, no intercalate ("Xoox": rows i<j, cols k<l with
# a[i][k] = a[j][l] and a[i][l] = a[j][k]), first row 1..9 (digit relabelling
# symmetry), and at least T pairs of torus-diagonally adjacent equal cells
# ((r,c) and (r+1 mod 9, c+-1 mod 9)).  Usage: python3 enc.py T > f.cnf
import sys, itertools
T = int(sys.argv[1]); NOX = len(sys.argv) > 2
nv = 0
def new():
    global nv; nv += 1; return nv
X = [[[new() for d in range(9)] for c in range(9)] for r in range(9)]
cl = []
for r in range(9):
    for c in range(9):
        cl.append([X[r][c][d] for d in range(9)])
        for d, e in itertools.combinations(range(9), 2): cl.append([-X[r][c][d], -X[r][c][e]])
groups = [[(r, c) for c in range(9)] for r in range(9)] + [[(r, c) for r in range(9)] for c in range(9)] + \
         [[(3*a + i, 3*b + j) for i in range(3) for j in range(3)] for a in range(3) for b in range(3)]
for g in groups:
    for d in range(9):
        cl.append([X[r][c][d] for r, c in g])
        for (r1, c1), (r2, c2) in itertools.combinations(g, 2): cl.append([-X[r1][c1][d], -X[r2][c2][d]])
for c in range(9): cl.append([X[0][c][c]])
for i, j in ([] if NOX else itertools.combinations(range(9), 2)):
    for k, l in itertools.combinations(range(9), 2):
        for d in range(9):
            for e in range(9):
                if d != e: cl.append([-X[i][k][d], -X[j][l][d], -X[i][l][e], -X[j][k][e]])
Y = []
for r in range(9):
    for c in range(9):
        for s in (1, -1):
            y = new(); Y.append(y); r2, c2 = (r + 1) % 9, (c + s) % 9
            for d in range(9): cl.append([-y, -X[r][c][d], X[r2][c2][d]])
# sequential counter: S[i][j] = at least j of Y[0..i-1] are true (only the needed direction)
n = len(Y); S = [[None] * (T + 1) for _ in range(n + 1)]
for i in range(n + 1):
    for j in range(1, T + 1):
        if j > i: continue
        S[i][j] = new()
for i in range(1, n + 1):
    for j in range(1, T + 1):
        if S[i][j] is None: continue
        prev = S[i - 1][j]
        # S[i][j] -> prev or Y[i-1]
        cl.append([-S[i][j]] + ([prev] if prev else []) + [Y[i - 1]])
        # S[i][j] -> prev or S[i-1][j-1]
        if j > 1:
            pp = S[i - 1][j - 1]
            cl.append([-S[i][j]] + ([prev] if prev else []) + ([pp] if pp else []))
cl.append([S[n][T]])
print(f"p cnf {nv} {len(cl)}")
for c in cl: print(" ".join(map(str, c)), 0)
