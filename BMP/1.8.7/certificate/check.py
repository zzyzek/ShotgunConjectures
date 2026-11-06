#!/usr/bin/env python3
# Check the real-DFT construction for d = 1..400: the d+1 points
# v_k = (1/sqrt 2)(b_1(k), ..., b_d(k)) are pairwise at distance 1 and
# every coordinate is at most 1/sqrt(d+1) in absolute value, so the
# simplex fits in a cube of side 2/sqrt(d+1).  Also prints the resulting
# lower bound log f(d)/d >= log floor(sqrt(d+1)/2) next to the volume
# upper bound log(d! 2^(d/2) / sqrt(d+1))/d.
#
import math
import numpy as np

def basis(n):
  k = np.arange(n)
  cols = []
  for j in range(1, (n+1)//2):
    cols.append(math.sqrt(2/n) * np.cos(2*math.pi*j*k/n))
    cols.append(math.sqrt(2/n) * np.sin(2*math.pi*j*k/n))
  if n % 2 == 0:
    cols.append(((-1.0)**k) / math.sqrt(n))
  return np.array(cols).T

worst = 0.0
for d in range(1, 401):
  n = d + 1
  B = basis(n)
  assert B.shape == (n, d)
  M = np.hstack([np.full((n, 1), 1/math.sqrt(n)), B])
  worst = max(worst, np.abs(M.T @ M - np.eye(n)).max())
  V = B / math.sqrt(2)
  D = np.sqrt(((V[:, None, :] - V[None, :, :])**2).sum(-1))
  off = D[~np.eye(n, dtype=bool)]
  worst = max(worst, np.abs(off - 1).max())
  assert np.abs(V).max() <= 1/math.sqrt(n) + 1e-12
  if d in (3, 10, 100, 400):
    m = math.isqrt(n // 4)
    lo = math.log(m) if m > 0 else float('-inf')
    hi = (math.lgamma(d+1) + 0.5*d*math.log(2) - 0.5*math.log(n)) / d
    print('d=%d  copies per side m=%d  log f/d in [%.3f, %.3f]' % (d, m, lo, hi))
print('max orthonormality/edge error over d<=400: %.2e' % worst)
assert worst < 1e-9
print('OK')
