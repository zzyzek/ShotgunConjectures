# A214900: every n <= 10^5 is x^2 + y^2 + z^2 + w^4, and the reduction used in
# the proof (w = 0, w = 1, or n = 16 m) always works for n <= 10^5 given that
# three-square representability is exactly "not 4^a(8b+7)" (checked to 10^5).
#
from math import isqrt
N = 10**5
two = bytearray(N + 1)
for x in range(isqrt(N) + 1):
  for y in range(x, isqrt(N - x * x) + 1): two[x * x + y * y] = 1
three = bytearray(N + 1)
for z in range(isqrt(N) + 1):
  zz = z * z
  for m in range(0, N - zz + 1):
    if two[m]: three[m + zz] = 1
def excl(m):
  if m == 0: return False
  while m % 4 == 0: m //= 4
  return m % 8 == 7
print("three squares <=> not 4^a(8b+7), m <= 10^5:", all(three[m] == (not excl(m)) for m in range(N + 1)))
four = all(any(three[n - w ** 4] for w in range(0, int(n ** 0.25) + 2) if w ** 4 <= n) for n in range(N + 1))
print("every n <= 10^5 is x^2+y^2+z^2+w^4:", four)
