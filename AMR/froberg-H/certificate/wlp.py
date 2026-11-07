# WLP check for T_{n,d,k} = S/(x_1^d,...,x_n^d)^k with l = x_1+...+x_n (for monomial ideals,
# WLP holds iff it holds for this l).  Rank of x l : A_t -> A_{t+1} over GF(p); a maximal rank
# mod p implies maximal rank over Q (rank over Q >= rank mod p for an integer matrix).
import sys, itertools
import numpy as np
P = 32749
def basis(n, d, k):
  # monomials not in I^k: exponent vector a with sum_i floor(a_i/d) < k
  B = {}
  def rec(i, a, s):
    if i == n:
      B.setdefault(sum(a), []).append(tuple(a)); return
    for e in range(0, d*k):
      if s + e // d < k:
        a.append(e); rec(i+1, a, s + e // d); a.pop()
  rec(0, [], 0)
  return B
def rank_mod(M):
  M = M.copy() % P
  r = 0; rows, cols = M.shape
  for c in range(cols):
    if r == rows: break
    piv = np.nonzero(M[r:, c])[0]
    if len(piv) == 0: continue
    pr = r + piv[0]
    if pr != r: M[[r, pr]] = M[[pr, r]]
    inv = pow(int(M[r, c]), P-2, P)
    M[r] = (M[r] * inv) % P
    nz = np.nonzero(M[:, c])[0]
    nz = nz[nz != r]
    if len(nz):
      M[nz] = (M[nz] - np.outer(M[nz, c], M[r])) % P
    r += 1
  return r
def check(n, d, k, verbose=False):
  B = basis(n, d, k)
  top = max(B)
  fails = []
  for t in range(0, top):
    src = B.get(t, []); dst = B.get(t+1, [])
    if not src or not dst: continue
    idx = {m: i for i, m in enumerate(dst)}
    M = np.zeros((len(dst), len(src)), dtype=np.int64)
    for j, m in enumerate(src):
      for i in range(n):
        mm = list(m); mm[i] += 1; mm = tuple(mm)
        if mm in idx: M[idx[mm], j] += 1
    r = rank_mod(M)
    full = min(len(src), len(dst))
    if verbose: print(' t', t, len(src), '->', len(dst), 'rank', r, 'max', full, flush=True)
    if r < full: fails.append((t, len(src), len(dst), r))
  return fails
if __name__ == '__main__':
  d, k = int(sys.argv[1]), int(sys.argv[2])
  for n in map(int, sys.argv[3].split(',')):
    f = check(n, d, k)
    print('n', n, 'd', d, 'k', k, 'WLP' if not f else 'FAILS %s' % f, flush=True)
