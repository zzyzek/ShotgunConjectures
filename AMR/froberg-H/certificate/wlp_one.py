# Rank of x(x_1+...+x_n): A_t -> A_{t+1} in T_{n,2,2} for one degree t (GF(32749)).
import sys
sys.path.insert(0, __import__('os').path.dirname(__file__))
from wlp import basis, rank_mod
import numpy as np
n, t = int(sys.argv[1]), int(sys.argv[2])
B = basis(n, 2, 2)
src, dst = B[t], B[t+1]
idx = {m: i for i, m in enumerate(dst)}
M = np.zeros((len(dst), len(src)), dtype=np.int64)
for j, m in enumerate(src):
  for i in range(n):
    mm = list(m); mm[i] += 1; mm = tuple(mm)
    if mm in idx: M[idx[mm], j] += 1
r = rank_mod(M)
print('n', n, 't', t, 'dims', len(src), '->', len(dst), 'rank', r, 'max rank' if r == min(len(src), len(dst)) else 'NOT max rank')
