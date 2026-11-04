# A100056: maximum of sum |pi(i+1) - pi(i)| over permutations of 1..n, versus a(n)
# from the A054065 permutation (order 1..n by frac(h*tau)).  n <= 9.
from itertools import permutations
from math import sqrt
tau = (1 + sqrt(5)) / 2
def s(p): return sum(abs(p[i+1] - p[i]) for i in range(len(p) - 1))
for n in range(2, 10):
  p = sorted(range(1, n + 1), key=lambda h: (h * tau) % 1)
  print(n, "A054065 row", p, "sum", s(p), "max", max(s(q) for q in permutations(range(1, n + 1))), "floor(n^2/2)-1 =", n*n//2 - 1)
print("(4,2,5,1,3):", s((4, 2, 5, 1, 3)))
