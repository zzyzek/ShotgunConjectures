# A214449(n) = least m with n! <= m^m (n >= 1); A118168(n) = argmin_x |x^x - n!|
# (n >= 0).  Conjecture: A214449(n) = A118168(n+1) ("A118168 with the first two
# 1s deleted").  Exact integers, n <= 1500.
#
N = 1500
f = [1]
for n in range(1, N + 2): f.append(f[-1] * n)
def least(F):
  m = 1
  while m ** m < F: m += 1
  return m
def argmin(F):
  m = least(F)
  return m - 1 if (m > 1 and abs((m - 1) ** (m - 1) - F) <= abs(m ** m - F)) else m
A = {n: least(f[n]) for n in range(1, N + 1)}
B = {n: argmin(f[n]) for n in range(0, N + 2)}
print("A118168 starts", [B[n] for n in range(8)], " A214449 starts", [A[n] for n in range(1, 7)])
bad = [n for n in range(1, N + 1) if A[n] != B[n + 1]]
print("n <= %d with A214449(n) != A118168(n+1):" % N, len(bad), bad[:8])
print("n = 188:", A[188], B[189])
