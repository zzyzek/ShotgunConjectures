# Build Golomb's sequence (A001462), the van Lamoen-Hanna triangle of A113676 and the
# Levine array (A014643/A014644); check both conjectures for the first rows.
def gamma(l):
  out = []
  for i, c in enumerate(l): out += [i + 1] * c
  return out
R = [[2]]
for k in range(9): R.append(gamma(R[-1]))
A014644 = [None] + [r[-1] for r in R[1:]]
G = R[-1]
H = [G[0]] + G[2:]
rows, pos = [[1]], 1
while True:
  n = sum(rows[-1])
  if pos + n > len(H): break
  rows.append(H[pos:pos + n]); pos += n
a = [len(r) for r in rows]
print("a =", a)
print("A014644 =", A014644[1:])
for n in range(2, min(len(rows), len(A014644) - 3) + 1):
  assert a[n - 1] == A014644[n + 2] - A014644[n + 1], n
  assert rows[n - 1][-1] == A014644[n + 1], n
assert rows[0][-1] == A014644[1]
print("checked rows 1..%d" % min(len(rows), len(A014644) - 3))
