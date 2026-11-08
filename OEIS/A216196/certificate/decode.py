# Decode a cadical model into a 9x9 grid and re-verify: Sudoku, intercalate
# count, torus-diagonal equal pairs.  Usage: python3 decode.py out_file
import sys, itertools
vals = set()
for line in open(sys.argv[1]):
    if line.startswith("v "): vals.update(int(t) for t in line.split()[1:] if int(t) > 0)
g = [[next(d + 1 for d in range(9) if (r * 81 + c * 9 + d + 1) in vals) for c in range(9)] for r in range(9)]
for row in g: print(" ".join(map(str, row)))
sud = all(len(set(r)) == 9 for r in g) and all(len({g[i][j] for i in range(9)}) == 9 for j in range(9)) and \
      all(len({g[3*a+i][3*b+j] for i in range(3) for j in range(3)}) == 9 for a in range(3) for b in range(3))
x = sum(1 for i, j in itertools.combinations(range(9), 2) for k, l in itertools.combinations(range(9), 2)
        if g[i][k] == g[j][l] and g[i][l] == g[j][k])
dg = sum(1 for r in range(9) for c in range(9) for s in (1, -1) if g[r][c] == g[(r+1) % 9][(c+s) % 9])
print("sudoku", sud, "xoox", x, "torus diagonal pairs", dg)
