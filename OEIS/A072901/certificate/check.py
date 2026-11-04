# A072901: composite n (not a square) with disc Q(sqrt n) = 4n are squarefree.
# disc = d if d == 1 (mod 4) else 4d, d the squarefree kernel of n
# (n = d s^2).  Checks n < 10^5: disc == 4n iff n squarefree and n == 2,3 (mod 4).
#
def core(n):
  d, s = n, 1
  q = 2
  while q * q <= d:
    while d % (q*q) == 0: d //= q*q; s *= q
    q += 1
  return d
bad = []
for n in range(2, 10**5):
  d = core(n)
  if d == 1: continue
  disc = d if d % 4 == 1 else 4*d
  if (disc == 4*n) != (d == n and n % 4 in (2, 3)): bad.append(n)
print("mismatches:", bad)
