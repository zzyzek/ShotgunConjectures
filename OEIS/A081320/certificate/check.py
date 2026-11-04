# A081320: largest 3-smooth divisor of F(n).  Checks n <= 3000:
# a(n) = a(n-12) for n > 12, 12 does not divide n; a(12k) = 144 * A065331(k).
#
def sm(x):
  r = 1
  while x % 2 == 0: x //= 2; r *= 2
  while x % 3 == 0: x //= 3; r *= 3
  return r
F = [0, 1]
for i in range(3001): F.append(F[-1] + F[-2])
a = [None] + [sm(F[n]) for n in range(1, 3001)]
print(all(a[n] == a[n-12] for n in range(13, 3001) if n % 12) and
      all(a[12*k] == 144 * sm(k) for k in range(1, 251)))
