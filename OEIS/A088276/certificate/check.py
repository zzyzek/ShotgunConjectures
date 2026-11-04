# A088276: r = 9351 (== 0 mod 3, odd, not divisible by 5): 10^k + r is divisible by
# 7, 11, 13 or 37 for every k (period 6).  Index of r among odd numbers not divisible
# by 5, with offset 0 (a(0) is r = 1).
#
r = 9351
print("r mod 3 =", r % 3, " index n =", sum(1 for j in range(1, r) if j % 2 and j % 5))
print("covered k < 6:", all(any((pow(10, k, q) + r) % q == 0 for q in (7, 11, 13, 37)) for k in range(6)))
print("direct k <= 3000:", all(any((10**k + r) % q == 0 for q in (7, 11, 13, 37)) for k in range(3001)))
