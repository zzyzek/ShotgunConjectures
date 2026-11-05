# OEIS A029766 (printed terms a(0..19)) against several readings of
# "unary-binary rooted trees with n nodes":
#   (a) labelled, unordered children (e.g.f. T = x(1 + T + T^2/2), A036774);
#   (b) labelled, ordered (plane) children: n! Motzkin(n-1);
#   (c) n! u(n), u(n) = number of unlabelled unary-binary trees whose binary nodes have two equal
#       branches (u(1) = 1, u(n) = u(n-1) + [n odd] u((n-1)/2)), by explicit enumeration of shapes;
# and Kotesovec's n! A040039(n-1), A040039 = first differences of A033485.
#
from fractions import Fraction
from math import factorial
DATA = [0,1,2,12,48,360,2160,25200,201600,2540160,25401600,399168000,
4790016000,80951270400,1133317785600,23538138624000,376610217984000,
8180810846208000,147254595231744000,3649353012264960000]
N = len(DATA) - 1
t = [Fraction(0)] * (N + 1)
for n in range(1, N + 1):
  t[n] = (1 if n == 1 else 0) + t[n-1] + sum(t[i] * t[n-1-i] for i in range(1, n-1)) / 2
lab = [int(t[n] * factorial(n)) for n in range(N + 1)]
mot = [1, 1]
for n in range(2, N + 1):
  mot.append(mot[-1] + sum(mot[i] * mot[n-2-i] for i in range(n-1)))
plane = [0] + [factorial(n) * mot[n-1] for n in range(1, N + 1)]
# Shapes: ('l',), ('u', s), ('b', s, s); enumerate all unordered unary-binary shapes and filter.
#
shapes = {1: [('l',)]}
for n in range(2, N + 1):
  out = [('u', s) for s in shapes[n-1]]
  for i in range(1, n - 1):
    j = n - 1 - i
    if i > j: break
    for x in shapes[i]:
      for y in shapes[j]:
        if i < j or x <= y: out.append(('b', x, y))
  shapes[n] = out
def sym(s):
  if s[0] == 'l': return True
  if s[0] == 'u': return sym(s[1])
  return s[1] == s[2] and sym(s[1])
u = [0] + [sum(1 for s in shapes[n] if sym(s)) for n in range(1, N + 1)]
A = [0, 1]
for n in range(2, N + 3): A.append(A[n-1] + A[n//2])
A040039 = [A[n+2] - A[n+1] for n in range(N + 1)]
assert all(DATA[n] == factorial(n) * A040039[n-1] for n in range(1, N + 1))
assert all(DATA[n] == factorial(n) * u[n] for n in range(1, N + 1))
first = lambda xs: next(n for n in range(1, N + 1) if xs[n] != DATA[n])
print("labelled unordered (A036774):", lab[1:6], "first mismatch n =", first(lab))
print("labelled plane n! M(n-1):   ", plane[1:6], "first mismatch n =", first(plane))
print("n! u(n), equal-branch shapes:", [factorial(n) * u[n] for n in range(1, 6)], "matches all", N, "terms")
print("OK: a(n) = n! A040039(n-1) for n = 1 ..", N)
