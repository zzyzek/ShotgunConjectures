# A105594/A105595/A105596 from the definitions, n <= 120:
# T(n,k) = (sum_j |mu(C(n,j))| * (C(n,j)... ) as in A105594), b(n) = row sums,
# c(m) = sum_k (-1)^k b(k) b(m-k); checks b odd, c(odd) = 0, c(even) == 1 (mod 4),
# and c(2n) against the A105596 data.
from math import comb
def sqfree_binom(n, j):
  x = comb(n, j)
  for p in range(2, n + 1):
    if x % (p * p) == 0: return 0
  return 1
N = 120
b = []
for n in range(N):
  s = [sqfree_binom(n, j) for j in range(n + 1)]
  b.append(sum(sum(s[j] * (comb(j, k) % 2) for j in range(n + 1)) % 2 for k in range(n + 1)))
c = [sum((-1)**k * b[k] * b[m - k] for k in range(m + 1)) for m in range(N)]
data = [1,5,13,17,25,25,33,21,9,-15,-23,-3,-11,-31,-47,-35,5,-47,-83,-75]
print("b odd:", all(x % 2 for x in b), " c(odd) = 0:", all(c[m] == 0 for m in range(1, N, 2)),
      " c(2n) == 1 mod 4:", all(c[m] % 4 == 1 for m in range(0, N, 2)), " data match:", [c[2*i] for i in range(20)] == data)
