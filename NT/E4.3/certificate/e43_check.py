# NT-E4.3 recheck: A(x) = (x/4, x/2] U {odd a in (x/2, 3x/4]} is primitive
# and S(A) = sum_{n<=x} #{a in A : a < n} = sum_{a in A} (x - a) exceeds x^2/6.
#
def A(x): return [a for a in range(1, x+1) if (4*a > x and 2*a <= x) or (2*a > x and 4*a <= 3*x and a % 2 == 1)]
def primitive(S):
  s = set(S)
  return not any(m in s for a in S for m in range(2*a, max(S)+1, a))
for x in (12, 100, 1000, 1500, 10000):
  S = A(x)
  direct = sum(sum(1 for a in S if a < n) for n in range(1, x+1)) if x <= 1500 else None
  tot = sum(x - a for a in S)
  print(x, "primitive", primitive(S), "S =", tot, "direct", direct, "S/x^2 = %.4f" % (tot/x/x), "x^2/6 = %.1f" % (x*x/6))
