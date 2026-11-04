# A000120 (wiki conjecture list): write the base-b digit sum s_b as a
# triangle, row 0 = s_b(0), row r = s_b(b^(r-1)) .. s_b(b^r - 1).
# Column k of row r is s_b(b^(r-1) + k), defined when k < (b-1) b^(r-1).
# Claim: in each column all positive entries are equal (to 1 + s_b(k)).
# Checks b = 2..12, rows r <= R with b^R <= 10^6.
#
def s(n, b):
  t = 0
  while n: t += n % b; n //= b
  return t

ok = True
for b in range(2, 13):
  R = 1
  while b ** (R + 1) <= 10**6: R += 1
  for r in range(1, R + 1):
    for k in range((b - 1) * b ** (r - 1)):
      if s(b ** (r - 1) + k, b) != 1 + s(k, b): ok = False
print("all columns constant (= 1 + s_b(k)):", ok)
