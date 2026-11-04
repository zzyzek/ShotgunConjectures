# Verify the C2 witness: 14 distinct squares tile a 799 x 689 rectangle.
# Exact check by backtracking placement (fill lowest-then-leftmost empty corner).
import sys
W, H = 799, 689
S = [5, 7, 23, 28, 30, 37, 44, 67, 72, 220, 287, 292, 397, 402]
print("area ok:", sum(s*s for s in S) == W*H)
sys.setrecursionlimit(10000)
# skyline representation: list of [x, width, height] segments
def solve(sky, rem, placed):
    if not rem:
        return placed
    i = min(range(len(sky)), key=lambda k: (sky[k][2], sky[k][0]))
    x, w, h = sky[i]
    for s in sorted(rem, reverse=True):
        if s > w or h + s > H:
            continue
        new = sky[:i] + [[x, s, h + s]] + ([[x + s, w - s, h]] if s < w else []) + sky[i+1:]
        merged = []
        for seg in new:
            if merged and merged[-1][2] == seg[2]:
                merged[-1][1] += seg[1]
            else:
                merged.append(list(seg))
        r = solve(merged, rem - {s}, placed + [(s, x, h)])
        if r:
            return r
    return None
res = solve([[0, W, 0]], frozenset(S), [])
print("tiling found:", res is not None)
if res:
    for s, x, y in res:
        print(f"square {s} at x={x}, y={y}")
