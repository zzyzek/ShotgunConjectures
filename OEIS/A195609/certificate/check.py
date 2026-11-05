# A195608 (evil, A001969) and A195609 (odious, A000069): compute
# S = {n >= 1 : 4*sum_{i<=n} A(i) = A(n)A(n+1)} directly, compare with the
# closed form {2j+1 : s(j)=0} u {2j+2 : s(j)=s(j+1)=0}, s = t (evil) or
# 1-t (odious), t = Thue-Morse, and with the OEIS b-file if one is given
# (argv: b195608.txt b195609.txt).  Then checks conjectures 1)-3) and the
# sharper statement A(m+1)-A(m-1) = 5 iff m-1 not in S (m in S, m >= 2).
#
import sys

def t(k):
  return bin(k).count('1') & 1

N = 400000
bfiles = sys.argv[1:]
for idx, (name, par) in enumerate((("A195608", 0), ("A195609", 1))):
  # A[n] for n = 1.., the n-th evil/odious number (offset 1).
  #
  A = [None] + [k for k in range(2 * N + 2) if t(k) == par][:N + 2]
  s = lambda k: (t(k) + par) % 2
  tot, S = 0, []
  for n in range(1, N + 1):
    tot += A[n]
    if 4 * tot == A[n] * A[n + 1]:
      S.append(n)
  closed = sorted([2 * j + 1 for j in range(N // 2) if s(j) == 0] +
                  [2 * j + 2 for j in range(N // 2) if s(j) == 0 and s(j + 1) == 0])
  closed = [n for n in closed if n <= N]
  assert S == closed, name + " closed form mismatch"
  if len(bfiles) > idx:
    b = [int(l.split()[1]) for l in open(bfiles[idx]) if l.strip() and l[0] != '#']
    assert S[:len(b)] == b, name + " b-file mismatch"
    print(name, "b-file terms matched:", len(b))
  Sset = set(S)
  diffs = sorted(set(y - x for x, y in zip(S, S[1:])))
  runs, cur = [], [S[0]]
  for x in S[1:]:
    if x == cur[-1] + 1:
      cur.append(x)
    else:
      runs.append(cur); cur = [x]
  lens = sorted(set(len(r) for r in runs))
  ok3 = all(A[r[0] + 1] - A[r[0] - 1] == 5 for r in runs if r[0] >= 2)
  okiff = all((A[m + 1] - A[m - 1] == 5) == ((m - 1) not in Sset) for m in S if m >= 2)
  print(name, "terms <=", N, ":", len(S), "first:", S[:12], "diffs:", diffs,
        "run lengths:", lens, "conj3:", ok3, "iff:", okiff,
        "run starts with m=1:", [r for r in runs if r[0] < 2])
