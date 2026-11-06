"""A115509: recompute a(n) from the definition (circular arrangements of 1..n,
started at 1, every cyclically adjacent pair good) by a bitmask DP over Hamiltonian
paths from 1, and check the formula a(n) = 0 for 2^(k+1) <= n < 3*2^k on the range.
"""
import sys

DATA = [1, 1, 2, 0, 0, 2, 4, 0, 0, 0, 0, 432, 1968, 24960, 161280, 0, 0, 0, 0, 0, 0, 0, 0]


def near(x, y):
  # every 1-bit of x has a 1-bit of y at the same or an adjacent position
  #
  i = 0
  while (x >> i) != 0:
    if ((x >> i) & 1) and not (y & (7 << i >> 1) if i > 0 else y & 3):
      return False
    i += 1
  return True


def good(x, y):
  return near(x, y) and near(y, x)


def a(n):
  if n == 1:
    return 1 if good(1, 1) else 0
  adj = [[good(x, y) for y in range(n + 1)] for x in range(n + 1)]
  # dp[mask][v]: paths from 1 visiting mask (bit j = number j+1), ending at v
  #
  full = (1 << n) - 1
  dp = [dict() for _ in range(1 << n)]
  dp[1][1] = 1
  for mask in range(1 << n):
    if not (mask & 1):
      continue
    for v, c in dp[mask].items():
      for w in range(2, n + 1):
        b = 1 << (w - 1)
        if (not (mask & b)) and adj[v][w]:
          dp[mask | b][w] = dp[mask | b].get(w, 0) + c
  return sum(c for v, c in dp[full].items() if adj[v][1])


def main():
  nmax = int(sys.argv[1]) if len(sys.argv) > 1 else 16
  for n in range(1, nmax + 1):
    v = a(n)
    assert v == DATA[n - 1], (n, v, DATA[n - 1])
    for k in range(1, 6):
      if (2 ** (k + 1) <= n) and (n < 3 * 2 ** k):
        assert v == 0
  print("A115509: a(1..%d) match the entry; formula zeros confirmed" % nmax)


main()
