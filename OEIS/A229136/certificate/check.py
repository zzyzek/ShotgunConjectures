# Brute-force A229136 for n <= 8, residue DP for n <= 200; compare with the
# OEIS data and with A131885(n) * 2^(n-1).
from itertools import product
data = [2,8,24,64,192,768,3584,16384,69632,278528,1081344,4194304,16515072,
  66060288,266338304,1073741824,4311744512,17246978048,68853694464,
  274877906944,1098437885952,4393751543808,17583596109824,70368744177664,
  281543696187392,1126174784749568]
for n in range(1, 9):
  assert sum(1 for x in product(range(4), repeat=n) if sum(v*v for v in x) % 4 == 1) == data[n-1]
A = [1, 2, 4, 6]
while len(A) < 202: A.append(4*A[-1] - 6*A[-2] + 4*A[-3])
c = [1, 0, 0, 0]
for n in range(1, 201):
  c = [sum(c[(r - v*v) % 4] for v in range(4)) for r in range(4)]
  if n <= len(data): assert c[1] == data[n-1]
  assert c[1] == A[n] * 2**(n-1)
print("OK: brute force n <= 8, DP and formula n <= 200, data n <= 26")
