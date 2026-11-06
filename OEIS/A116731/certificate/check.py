# Bubble sort on all permutations of 1..n: collect (flips, iterations) pairs
# for three loop conventions and compare with A116731 (n^3-3n^2+5n)/3 and
# with the inversion-table description (inv, max left-greater count).
import itertools
def bubble(p, shrink, count_final):
  a = list(p); flips = 0; it = 0; hi = len(a) - 1
  while True:
    sw = False
    for j in range(hi):
      if a[j] > a[j + 1]:
        a[j], a[j + 1] = a[j + 1], a[j]; flips += 1; sw = True
    if sw or count_final: it += 1
    if shrink: hi -= 1
    if not sw: break
  return flips, it
for n in range(1, 10):
  perms = list(itertools.permutations(range(1, n + 1)))
  res = []
  for shrink in (False, True):
    for cf in (False, True):
      res.append(len({bubble(p, shrink, cf) for p in perms}))
  stat = set()
  for p in perms:
    c = [sum(1 for k in range(i) if p[k] > p[i]) for i in range(n)]
    stat.add((sum(c), max(c)))
    assert bubble(p, False, False) == (sum(c), max(c))
  M = lambda b: sum(min(b, j) for j in range(n))
  formula = 1 + sum(M(b) - b + 1 for b in range(1, n))
  print(n, res, len(stat), formula, (n**3 - 3*n*n + 5*n) // 3)

# A116731 by its definition: permutations avoiding 321, 2143, 3124.
def contains(p, pat):
  k = len(pat)
  for idx in itertools.combinations(range(len(p)), k):
    vals = [p[i] for i in idx]
    if all((vals[a] < vals[b]) == (pat[a] < pat[b]) for a in range(k) for b in range(k)):
      return True
  return False
for n in range(1, 9):
  cnt = sum(1 for p in itertools.permutations(range(1, n + 1))
            if not any(contains(p, q) for q in ((3,2,1), (2,1,4,3), (3,1,2,4))))
  print("avoiders", n, cnt, (n**3 - 3*n*n + 5*n) // 3)
