#!/usr/bin/env python3
# CNF: k-colouring of [1, N] with no monochromatic solution of
# x1 + ... + x_{t-1} = x_t (x_i not necessarily distinct).
# Variable v(i, c) = i*k + c + 1 - k  (i in 1..N, c in 0..k-1).
# Symmetry breaking: colour(1) = 0, and colour c+1 first appears after colour c
# (encoded by "i uses colour c+1 only if some j < i uses colour c").
#
# usage: gen.py N k t > f.cnf
#
import sys, itertools

N, k, t = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])

def v(i, c):
  return (i - 1)*k + c + 1

cls = []
for i in range(1, N+1):
  cls.append([v(i, c) for c in range(k)])
  for c in range(k):
    for d in range(c+1, k):
      cls.append([-v(i, c), -v(i, d)])

# Solutions: multisets {x1..x_{t-1}} with sum <= N.
#
sols = set()
def rec(start, left, acc, s):
  if left == 0:
    if s <= N:
      sols.add(tuple(sorted(set(acc + [s]))))
    return
  for x in range(start, N+1):
    if s + x + (left - 1)*x > N:
      break
    rec(x, left - 1, acc + [x], s + x)
rec(1, t - 1, [], 0)
for S in sols:
  for c in range(k):
    cls.append([-v(i, c) for i in S])

# Symmetry breaking.
#
cls.append([v(1, 0)])
for i in range(2, N+1):
  for c in range(1, k):
    # colour c at i implies colour c-1 at some j < i.
    #
    cls.append([-v(i, c)] + [v(j, c-1) for j in range(1, i)])

print(f"p cnf {N*k} {len(cls)}")
for C in cls:
  print(" ".join(map(str, C)) + " 0")
