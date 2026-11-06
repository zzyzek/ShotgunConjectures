# a_r(n) = number of permutations with all cycle lengths = 1 (mod r), r = 3 (A193437), 4 (A193438),
# from a(n) = sum_k C(n-1, rk) (rk)! a(n-rk-1). Check v_p(a(n)) >= v_p(n!) >= floor(n/p)
# for primes p = 1 (mod r) below 60, n <= 400, and the data terms.
from math import comb, factorial
def seq(r, N):
  a = [1]
  for n in range(1, N+1):
    a.append(sum(comb(n-1, r*k)*factorial(r*k)*a[n-r*k-1] for k in range((n-1)//r + 1)))
  return a
def v(p, x):
  c = 0
  while x % p == 0: x //= p; c += 1
  return c
data = {3: [1,1,1,1,7,31,91,931,7441,38017,507241,5864761,43501591,713059711],
        4: [1,1,1,1,1,25,145,505,1345,43345,481825,3027025,13679425,528618025]}
for r in (3, 4):
  a = seq(r, 400)
  assert a[:14] == data[r]
  for p in [q for q in range(2, 60) if all(q % d for d in range(2, q)) and q % r == 1]:
    for n in range(401):
      assert v(p, a[n]) >= v(p, factorial(n)) >= n // p, (r, p, n)
print("ok")
