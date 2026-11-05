# A104895 check: the Lean definition of a(n) (data recursion
# a(0)=0, a(2n)=2a(n), a(2n+1)=-2a(n)-1) against the OEIS b-file, the
# printed %N recursion against the data, and the positions statement.
#
# Usage: python3 check.py [b104895.txt]
# (b-file from https://oeis.org/A104895/b104895.txt, n = 0..20000)
#
import sys

N = 1 << 16

# a: the data recursion used in A104895_mathlib.lean.
# nrule: the %N recursion as printed (a(2n)=-2a(n), a(2n+1)=2a(n)-1).
#
a     = [0] * N
nrule = [0] * N
for n in range(1, N):
  if (n % 2) == 0:
    a[n]     = 2 * a[n // 2]
    nrule[n] = -2 * nrule[n // 2]
  else:
    a[n]     = -2 * a[n // 2] - 1
    nrule[n] = 2 * nrule[n // 2] - 1

if len(sys.argv) > 1:
  bf = {}
  for line in open(sys.argv[1]):
    p = line.split()
    if (len(p) == 2) and (not line.startswith("#")):
      bf[int(p[0])] = int(p[1])
  print("b-file terms:", len(bf),
        " data recursion matches b-file:", all(a[n] == v for n, v in bf.items()),
        " printed %N matches b-file:", all(nrule[n] == v for n, v in bf.items()))
  bad = [n for n in sorted(bf) if nrule[n] != bf[n]]
  print("first index where printed %N differs:", bad[0], nrule[bad[0]], bf[bad[0]])

# A048724(k) = k XOR 2k; A065621(k) = (k-1) XOR (2k-1), the form used in
# Lean, compared with the entry's k XOR 2(k - (k AND -k)).
#
def A048724(k):
  return k ^ (2 * k)

def A065621(k):
  return (k - 1) ^ (2 * k - 1)

print("A065621 forms agree:",
      all(A065621(k) == (k ^ (2 * (k - (k & -k)))) for k in range(1, 100000)))

pos = {}
for n in range(N):
  pos.setdefault(a[n], n)
print("a injective on [0,2^16):", len(set(a)) == N,
      " pos(k)=A048724(k):", all(pos.get(k) == A048724(k) for k in range(0, 10000)),
      " pos(-k)=A065621(k):", all(pos.get(-k) == A065621(k) for k in range(1, 10000)))
