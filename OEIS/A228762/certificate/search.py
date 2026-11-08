# Backtracking search for an R-sequencing of Z_m1 x Z_m2: a cyclic order of
# the nonzero elements whose successive differences a_i - a_{i+1} (and
# a_last - a_first) are pairwise distinct.  Usage: python3 search.py m1 m2
import sys
m1, m2 = int(sys.argv[1]), int(sys.argv[2])
els = [(x, y) for x in range(m1) for y in range(m2) if (x, y) != (0, 0)]
sub = lambda a, b: ((a[0] - b[0]) % m1, (a[1] - b[1]) % m2)
N = len(els); seq = [els[0]]; used = {els[0]}; diffs = set()
def go():
    if len(seq) == N:
        d = sub(seq[-1], seq[0])
        return d not in diffs
    for e in els:
        if e in used: continue
        d = sub(seq[-1], e)
        if d in diffs: continue
        seq.append(e); used.add(e); diffs.add(d)
        if go(): return True
        seq.pop(); used.discard(e); diffs.discard(d)
    return False
sys.setrecursionlimit(10000)
print(go(), seq)
