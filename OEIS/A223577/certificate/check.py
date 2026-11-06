#!/usr/bin/env python3
# Recompute A223577 and A223578 from their OEIS definitions with
# f(m) = floor(cot(pi/(2m))), using 50-digit mpmath arithmetic, and check
# A223578(n) = 2*A223577(n) - n + 1 for the first N terms.
#
# Optional arguments: paths to b223577.txt and b223578.txt (OEIS b-files)
# to compare with the published terms. Also reports the A223577 FORMULA
# line a(n) = floor(cot(pi/(2*A223578(n)))), which fails for n >= 2
# (it needs ceiling, i.e. -f(-A223578(n))).
#
import sys
from mpmath import mp, cot, pi, floor

mp.dps = 50
N = 10000


def f(m):
  return int(floor(cot(pi / (2 * m))))


def main():
  J = 40000
  F = {m: f(m) for m in range(-J - 2, 0)}
  a78 = [k for k in range(2, J) if F[-k - 1] < F[-k] < F[-k + 1]][:N]
  pre = {}
  for m in range(-J - 2, 0):
    pre.setdefault(-F[m], []).append(m)
  top = -F[-J]
  a77 = [k for k in range(1, top) if len(pre.get(k, [])) == 1][:N]
  assert len(a77) == N and len(a78) == N
  ok = all(a78[i] == 2 * a77[i] - (i + 1) + 1 for i in range(N))
  print("identity A223578(n) = 2*A223577(n) - n + 1 for n <= %d:" % N, ok)
  bad = [i + 1 for i in range(N) if int(floor(cot(pi / (2 * a78[i])))) != a77[i]]
  print("A223577 FORMULA floor(cot(pi/(2*A223578(n)))) fails at", len(bad), "of", N, "n; first", bad[:5])
  if len(sys.argv) == 3:
    rd = lambda p: [int(l.split()[1]) for l in open(p) if l.strip() and not l.startswith('#')]
    b77, b78 = rd(sys.argv[1]), rd(sys.argv[2])
    print("b223577 agrees:", b77 == a77[:len(b77)], len(b77))
    print("b223578 agrees:", b78 == a78[:len(b78)], len(b78))
  sys.exit(0 if ok else 1)


main()
