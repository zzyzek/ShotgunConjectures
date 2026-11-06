# Recompute A179901/A179902 from the convolution definition, compare with the
# data of both entries, the closed form and the parity pattern.
def arr(r, m):
  u = lambda i: 1 if i == 0 else r
  v = lambda j: 1 if j == 0 else (0 if j == 1 else r)
  return sum(u(i) * v(m - i) for i in range(m + 1))
tri = [1,1,1,1,2,2,1,3,4,3,1,4,6,8,4,1,5,8,15,12,5,1,6,10,24,24,16,6,1,7,12,
  35,40,33,20,7,1,8,14,48,60,56,42,24,8,1,9,16,63,84,85,72,51,28,9,1,
  10,18,80,112,120,110,88,60,32,10,1,11,20,99,144,161,156,135,104,69,36,11]
flat = [arr(n + 1 - k, k - 1) for n in range(1, 14) for k in range(1, n + 1)]
assert flat[:len(tri)] == tri
a = lambda n: sum(arr(n + 1 - k, k - 1) for k in range(1, n + 1))
data = [1,2,5,11,23,46,87,155,261,418,641,947,1355,1886,2563,3411,4457,5730,
  7261,9083,11231,13742,16655,20011,23853,28226,33177,38755,45011,
  51998,59771,68387,77905,88386,99893,112491,126247,141230,157511,175163,194261,214882]
assert [a(n) for n in range(1, len(data) + 1)] == data
for n in range(1, 301):
  assert 12 * a(n) == n**4 - 8*n**3 + 35*n**2 - 52*n + 36
  assert a(n) % 2 == (0 if n % 4 == 2 else 1)
print("OK: triangle and row-sum data, closed form and parity for n <= 300")
