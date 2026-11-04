# A182334: triangular numbers T with T = s^2 +- 1, by brute force over k
# (T = k(k+1)/2, k < 10^6), then the order-9 recurrence from index 10 on.
#
from math import isqrt
a = []
for k in range(0, 10**6):
  T = k * (k + 1) // 2
  if any(v >= 0 and isqrt(v) ** 2 == v for v in (T - 1, T + 1)): a.append(T)
a = [None] + a
print("first terms:", a[1:15])
bad = [n for n in range(10, len(a)) if a[n] != 35*a[n-3] - 35*a[n-6] + a[n-9]]
print("recurrence fails at n (offset 1):", bad, " checked up to n =", len(a) - 1)
