# A225001 (dead, "Duplicate of A047203"): a(n) = floor(1/frac(e^(4/(5n)))).
# Claim a(n) = A047203(n) = floor((5n-2)/4) for n > 1, via
# 1/x - 1/2 < 1/(e^x - 1) < 1/x - 1/2 + x/12 (x > 0), x = 4/(5n).
#
import mpmath as mp
mp.mp.dps = 60
bad = []
for n in range(2, 100001):
  v = mp.floor(1 / mp.frac(mp.e ** (mp.mpf(4) / (5 * n))))
  if int(v) != (5 * n - 2) // 4: bad.append(n)
print("n in [2, 10^5] with a(n) != floor((5n-2)/4):", bad[:5])
print("n = 1:", int(mp.floor(1 / mp.frac(mp.e ** (mp.mpf(4) / 5)))), "vs", (5 - 2) // 4)
