#!/usr/bin/env python3
# CNF for "[1, N] has a 4-colouring with no monochromatic x + y + z = w"
# (x <= y <= z, repeats allowed), in the clause order of the Lean file
# E11_2 Cnf module:
#   alo  : for x = 1..N, [pos x 0, pos x 1, pos x 2, pos x 3]
#   amo  : for x = 1..N, a < b, [neg x a, neg x b]
#   symm : [pos 1 0], [pos 3 1], and for i = 2..N: [neg i 3, pos 1 2, ..., pos (i-1) 2]
#   tri  : one clause per (x, y, z, c) in the triple list T (default: all valid ones)
# Variable 4 (x - 1) + c + 1; DIMACS positive literal = "x has colour c".
#
# usage: gen2.py N [triples.txt] > f.cnf      (triples.txt: lines "x y z c")
#
import sys

N = int(sys.argv[1])

def v(x, c):
  return 4*(x - 1) + c + 1

def tri_clause(x, y, z, c):
  w = x + y + z
  if (x == y) and (y == z):
    return [-v(x, c), -v(w, c)]
  if x == y:
    return [-v(x, c), -v(z, c), -v(w, c)]
  if y == z:
    return [-v(x, c), -v(y, c), -v(w, c)]
  return [-v(x, c), -v(y, c), -v(z, c), -v(w, c)]

def all_triples():
  T = []
  for x in range(1, N//3 + 1):
    for y in range(x, (N - x)//2 + 1):
      for z in range(y, N - x - y + 1):
        for c in range(4):
          T.append((x, y, z, c))
  return T

if len(sys.argv) > 2:
  T = [tuple(map(int, l.split())) for l in open(sys.argv[2]) if l.strip()]
else:
  T = all_triples()

cls = []
for x in range(1, N+1):
  cls.append([v(x, c) for c in range(4)])
for x in range(1, N+1):
  for a in range(4):
    for b in range(a+1, 4):
      cls.append([-v(x, a), -v(x, b)])
cls.append([v(1, 0)])
cls.append([v(3, 1)])
for i in range(2, N+1):
  cls.append([-v(i, 3)] + [v(j, 2) for j in range(1, i)])
for t in T:
  cls.append(tri_clause(*t))

print(f"p cnf {4*N} {len(cls)}")
for C in cls:
  print(" ".join(map(str, C)) + " 0")
