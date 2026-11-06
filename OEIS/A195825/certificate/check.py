# Column k of A195825: g.f. 1 / sum_{j in Z} (-1)^j q^{(m j^2 - (m-2) j)/2}, m = k+2
# (Euler-type recurrence of the entry, generalized (k+4)-gonal numbers).
# Checks, for k = 1..K and n <= N:
#  (a) the column equals the number of partitions of n into parts = 0, 1, m-1 (mod m);
#  (b) plateaus (maximal runs of equal consecutive terms, length >= 2) are exactly the runs
#      starting at n = A(m+1) of length k+1-2A (A = 0, 1, ... while >= 2), with level
#      L(A) = sum_{B<=A} p3(B) (p3 = 3-colour partitions A000716), = A210843(A+1);
#  (c) the entry's data (first 10 columns, antidiagonals) and A210843's data.
import sys
K, N = int(sys.argv[1]), int(sys.argv[2])
def column_recurrence(k, N):
  m = k + 2
  coef = [0] * (N + 1)
  j = 0
  while True:
    done = True
    for jj in ([j] if j == 0 else [j, -j]):
      e = (m * jj * jj - (m - 2) * jj) // 2
      if e <= N: coef[e] += (-1) ** abs(jj); done = False
    if done and j > 0: break
    j += 1
  T = [0] * (N + 1); T[0] = 1
  for n in range(1, N + 1):
    T[n] = -sum(coef[i] * T[n - i] for i in range(1, n + 1) if coef[i])
  return T
def column_partitions(k, N):
  m = k + 2
  T = [1] + [0] * N
  for p in range(1, N + 1):
    if p % m in (0, 1, m - 1):
      for n in range(p, N + 1): T[n] += T[n - p]
  return T
p3 = [1] + [0] * 60
for a in range(1, 61):
  for _ in range(3):
    for n in range(a, 61): p3[n] += p3[n - a]
L = [sum(p3[:A + 1]) for A in range(61)]
A210843 = [1,4,13,35,86,194,415,844,1654,3133,5773,10372,18240,31449,53292]
assert L[:15] == A210843
for k in range(1, K + 1):
  m = k + 2
  T = column_recurrence(k, N)
  assert T == column_partitions(k, N), k
  runs = []; i = 0
  while i <= N:
    j = i
    while j + 1 <= N and T[j + 1] == T[i]: j += 1
    if j > i and j < N: runs.append((i, j - i + 1, T[i]))
    i = j + 1
  expect = [(A * (m + 1), k + 1 - 2 * A, L[A]) for A in range(0, k) if k + 1 - 2 * A >= 2]
  assert runs == expect, (k, runs, expect)
data = [1,1,1,2,1,1,3,1,1,1,5,2,1,1,1,7,3,1,1,1,1,11,4,2,1,1,1,1,15,5,3,1,1,1,1,1,22,7,4,2,1,1,1,1,1,30,10,4,3,1,1,1,1,1,1,42,13,5,4,2,1,1,1,1,1,1,56,16,7,4,3,1,1,1,1,1,1,1,77,21,10,4]
cols = {k: column_recurrence(k, 20) for k in range(1, 15)}
flat = []
for d in range(14):
  for k in range(1, d + 2): flat.append(cols[k][d + 1 - k])
assert flat[:len(data)] == data
print("k = 1..%d, n <= %d: all checks pass" % (K, N))
