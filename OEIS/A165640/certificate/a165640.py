# A165640: multisets of n values in {-2, 1, 3} with sum 3, versus the floor formula.
#
def cnt(n):
  return sum(1 for x in range(n + 1) for z in range(n + 1 - x) if -2*x + (n - x - z) + 3*z == 3)
f = lambda n: (4*(n+4))//5 - (2*(n+4))//3
print("agree for 1 <= n <= 400:", all(cnt(n) == f(n) for n in range(1, 401)), " n=0:", cnt(0), f(0))
