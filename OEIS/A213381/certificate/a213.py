import sys
N = int(sys.argv[1]); K = 200
first = {}; cnt = {}
for n in range(0, N):
  m = n + 2
  v = pow(m - 2, n, m)
  if v < K:
    cnt[v] = cnt.get(v, 0) + 1
    if v not in first: first[v] = n
missing = [k for k in range(K) if k not in first]
print("missing k<200 up to n<", N, ":", missing)
print("rare:", sorted([(cnt[k], k, first[k]) for k in cnt])[:25])
