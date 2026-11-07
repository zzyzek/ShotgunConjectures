import sys, itertools
def is_subseq(p, s):
  it = iter(s)
  return all(any(c == x for x in it) for c in p)
def rosary_ok(w, n):
  L = len(w); rots = [w[i:] + w[:i] for i in range(L)]
  return all(any(is_subseq(p, r) for r in rots) for p in itertools.permutations(range(1, n + 1)))
w = list(map(int, sys.argv[2:])); n = int(sys.argv[1])
print(n, len(w), rosary_ok(w, n))
