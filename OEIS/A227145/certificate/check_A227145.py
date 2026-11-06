# A227145: a(n) = n - 1 - sum_{i>=1} a^i(n-i), a(n) = 0 for n <= 1.
# 1. Compute a(n) by the recurrence (full sum i = 1..n) for n <= N; check the data.
# 2. Compare with c(n) = number of nonzero letters among w_0..w_(n-1), w = 0 sig(w),
#    sig: k -> (k+1) 0^(k+1)  (the word used in A227145_mathlib.lean).
# 3. Check a(F_m) = F_(m-2) for all F_m <= N.
import sys
N = int(sys.argv[1]) if len(sys.argv) > 1 else 3000
a = [0] * (N + 1)
def it(i, m):
  for _ in range(i):
    if m <= 1: return 0
    m = a[m]
  return m
for n in range(2, N + 1):
  a[n] = n - 1 - sum(it(i, n - i) for i in range(1, n + 1))
data = [0,1,1,2,2,2,3,3,4,4,4,4,5,5,6,6,7,7,7,8,8,9,9,9,9,9,10,10,11,11,12,12,13,13,13,
        14,14,15,15,15,16,16,17,17,17,17,18,18,19,19,20,20,20,21,21,22,22,22,22,22,22,23,23,
        24,24,25,25,26,26,27,27,27]
assert a[1:len(data) + 1] == data
w = [0]
while len(w) < N + 1:
  w = [0] + [x for k in w for x in [k + 1] + [0] * (k + 1)]
c = [0]
for i in range(N): c.append(c[-1] + (w[i] != 0))
assert all(a[n] == c[n] for n in range(N + 1))
F = [0, 1]
while F[-1] <= N: F.append(F[-1] + F[-2])
ok = [m for m in range(2, len(F)) if F[m] <= N]
assert all(a[F[m]] == F[m - 2] for m in ok)
print("data OK; a = c for n <= %d; a(F_m) = F_(m-2) for m = 2..%d" % (N, ok[-1]))
