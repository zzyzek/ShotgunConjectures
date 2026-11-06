# Check the Bergot array conjecture in A026002: the array m with
# m(n,1) = m(1,n) = n(n-1)+1 and m(i,j) = m(i,j-1) + m(i-1,j-1) + m(i-1,j)
# has m(n,n) = a(n); and 2 m(i,j) = D(i-1,j+1) + D(i+1,j-1) (Delannoy D).
# a(n) is taken from the b-file (argument 1) and Deutsch's formula.
#
import sys
from math import comb
N = 220
D = [[1]*(N+3) for _ in range(N+3)]
for i in range(1, N+3):
  for j in range(1, N+3):
    D[i][j] = D[i-1][j] + D[i-1][j-1] + D[i][j-1]
m = [[0]*(N+1) for _ in range(N+1)]
for n in range(1, N+1):
  m[n][1] = m[1][n] = n*(n-1) + 1
for i in range(2, N+1):
  for j in range(2, N+1):
    m[i][j] = m[i][j-1] + m[i-1][j-1] + m[i-1][j]
assert all(2*m[i][j] == D[i-1][j+1] + D[i+1][j-1] for i in range(1, N+1) for j in range(1, N+1))
deut = lambda n: sum(k*comb(n, k)*comb(n+k, k+1) for k in range(n+1)) // n
assert all(m[n][n] == D[n-1][n+1] == deut(n) for n in range(1, N+1))
if len(sys.argv) > 1:
  b = [tuple(map(int, l.split())) for l in open(sys.argv[1]) if l.strip() and not l.startswith('#')]
  assert all(m[n][n] == v for n, v in b), "b-file mismatch"
  print("b-file terms:", len(b))
print("ok, n <=", N)
