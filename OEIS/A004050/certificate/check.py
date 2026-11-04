# A004050 / A085634: solutions of 2^a + 3^b = 2^c + 3^d with a > c.
# (1) the valuation bounds used in the reduction: v_2(3^e - 1) <= log2(4e),
#     v_3(2^f - 1) <= log3(3f), checked for e, f <= 2000;
# (2) pairs (X, Y) with |2^X - 3^Y| <= 4X, X <= 60 (Ellison covers X >= 28);
# (3) all solutions with a <= 27 (then b < d <= a, c < a).
#
def v(n, p):
  k = 0
  while n % p == 0: n //= p; k += 1
  return k

print("LTE bounds:", all(2 ** v(3**e - 1, 2) <= 4*e for e in range(1, 2001)) and
                    all(3 ** v(2**f - 1, 3) <= 3*f for f in range(1, 2001)))
print("small pairs:", [(X, Y) for X in range(61) for Y in range(40) if abs(2**X - 3**Y) <= 4*X])
sols = sorted({2**a + 3**b for a in range(28) for c in range(a) for d in range(a + 1)
               for b in range(d) if 2**a + 3**b == 2**c + 3**d})
print("values with two representations (a <= 27):", sols)
