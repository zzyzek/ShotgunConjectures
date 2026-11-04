# A110320 from definitions, n <= 40:
#  a(n) = total number of blocks over RNA secondary structures on [n]
#         (noncrossing, blocks of size 1 or 2, a pair (i,j) needs j - i >= 2);
#  A051286(n) = number of n-element order ideals of the fence of order 2n;
#  A051292(n) = number of n-element order ideals of the crown of size 2n.
# Checks a(n) = (A051292(n+2) - A051286(n+1))/2.
#
N = 44
S = [1, 1] + [0] * N; B = [0, 1] + [0] * N
for n in range(2, N + 1):
  S[n] = S[n-1]; B[n] = B[n-1] + S[n-1]
  for k in range(1, n - 1):
    l, r = k - 1, n - 1 - k
    S[n] += S[l] * S[r]; B[n] += B[l] * S[r] + S[l] * B[r] + S[l] * S[r]
def ideals(m, cyclic, up_first):
  # elements 0..m-1, x_i < x_{i+1} if (i even) == up_first, else x_i > x_{i+1}; cyclic adds (m-1, 0)
  def less(i, j):
    # is x_i covered-below x_j for adjacent i, j = i+1 (mod m)?
    return (i % 2 == 0) == up_first
  edges = [(i, i + 1) for i in range(m - 1)] + ([(m - 1, 0)] if cyclic else [])
  cnt = {}
  for start in (0, 1):
    dp = {(start, start): 1}
    for i in range(1, m):
      nd = {}
      for (prev, sz), v in dp.items():
        for cur in (0, 1):
          lo, hi = (i - 1, i) if less(i - 1, i) else (i, i - 1)
          vals = {i - 1: prev, i: cur}
          if vals[hi] == 1 and vals[lo] == 0: continue
          nd[(cur, sz + cur)] = nd.get((cur, sz + cur), 0) + v
      dp = nd
    for (last, sz), v in dp.items():
      if cyclic:
        lo, hi = (m - 1, 0) if less(m - 1, 0) else (0, m - 1)
        vals = {m - 1: last, 0: start}
        if vals[hi] == 1 and vals[lo] == 0: continue
      cnt[sz] = cnt.get(sz, 0) + v
  return cnt
A286 = [ideals(2*n, False, True).get(n, 0) if n else 1 for n in range(N)]
A292 = [ideals(2*n, True, True).get(n, 0) if n else 2 for n in range(N)]
print("A051286:", A286[:10]); print("A051292:", A292[:10]); print("A110320:", B[1:11])
print("identity n = 1..40:", all(2 * B[n] == A292[n + 2] - A286[n + 1] for n in range(1, 41)))
