#!/usr/bin/env python3
# From the unsat core of the full CNF (core.py output: original clause ids used by the
# LRAT proof), write the solution tuples "x y z c" of the core triple clauses, in CNF order.
# usage: select_core.py N core_ids.txt > tri.txt
import sys
N = int(sys.argv[1])
T = []
for x in range(1, N//3 + 1):
  for y in range(x, (N - x)//2 + 1):
    for z in range(y, N - x - y + 1):
      for c in range(4):
        T.append((x, y, z, c))
fixed = N + 6*N + 2 + (N - 1)
core = [int(l) for l in open(sys.argv[2]) if l.strip()]
for i in core:
  if i > fixed:
    print(*T[i - fixed - 1])
