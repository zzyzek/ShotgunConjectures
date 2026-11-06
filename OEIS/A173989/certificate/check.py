# A173989(n) = v2(denominator of ((1+sqrt3)/2)^n + ((1-sqrt3)/2)^n)
#            = v2(denominator of s_n / 2^n), s_0 = s_1 = 2,
# s_{n+2} = 2 s_{n+1} + 2 s_n.  Checks the closed form
# a(4j+3) = a(4j+4) = a(4j+6) = 2j+1, a(4j+5) = 2j+2 for n = 3..10000,
# a(1) = a(2) = 0, and the first 78 OEIS data terms (cached 2026-11-05).
#
from fractions import Fraction

DATA = [0,0,1,1,2,1,3,3,4,3,5,5,6,5,7,7,8,7,9,9,10,9,11,11,12,11,13,13,14,
        13,15,15,16,15,17,17,18,17,19,19,20,19,21,21,22,21,23,23,24,23,25,
        25,26,25,27,27,28,27,29,29,30,29,31,31,32,31,33,33,34,33,35,35,36,
        35,37,37,38,37]

N = 10000
s = [2, 2]
while len(s) <= N:
  s.append(2 * s[-1] + 2 * s[-2])

def v2(m):
  return ((m & -m).bit_length() - 1)

def a(n):
  return v2(Fraction(s[n], 2 ** n).denominator)

def closed(n):
  j, r = divmod(n - 3, 4)
  return ( (2 * j + 2) if (r == 2) else (2 * j + 1) )

assert (a(1) == 0) and (a(2) == 0)
for n in range(3, N + 1):
  assert a(n) == closed(n), n
assert [a(n) for n in range(1, len(DATA) + 1)] == DATA
print("closed form holds for n = 3 ..", N, "; data terms match:", len(DATA))
