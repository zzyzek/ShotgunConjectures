# A023402 / A081532: T(n,3) = 3rd divisor of the smallest number with n divisors.
# A023402(1..2): the last k digits of a power of 2 drawn from {3,4}.
#
def ndiv(m): return sum(1 for d in range(1, m + 1) if m % d == 0)
def smallest(n):
  m = 1
  while ndiv(m) != n: m += 1
  return m
T = {n: [d for d in range(1, smallest(n) + 1) if smallest(n) % d == 0][2] for n in range(3, 13)}
print("T(n,3), n = 3..12:", T)
ends = sorted({pow(2, e, 100) for e in range(2, 200) if set(str(pow(2, e, 100)).zfill(2)) <= set("34")})
print("2-digit endings of 2^e (e >= 2) using only 3,4:", ends)
