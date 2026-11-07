# Check of the A192062 prime-chain conjecture for small cases.
# T(i,j): A192062 recurrence. A(i,j): A191971 recurrence.
# Checks (1) T(2n,j) = A(n,j) T(n,j); (2) G_1 = T, G_{k+1}(n) = G_k(p_k n)/G_k(n)
# is an integer, for primes p_1..p_K = 2,3,5,7,11 and the stated n, j ranges;
# (3) G_2 = A.
import sys
PR = [2, 3, 5, 7, 11]
def T_col(j, N):
  t = [0, 1]
  while len(t) <= N:
    i = len(t)
    t.append(t[i-2] + t[i-1] if i % 2 == 0 else t[i-2] + j*t[i-1])
  return t
def A_col(j, N):
  a = [2, 1]
  while len(a) <= N:
    i = len(a)
    a.append(j*a[i-1] + a[i-2] if i % 2 == 0 else a[i-1] + a[i-2])
  return a
bad = 0
for j in range(0, 13):
  K, NMAX = 5, 12
  N = NMAX * 2*3*5*7*11
  t = T_col(j, N); a = A_col(j, N)
  for n in range(1, N//2 + 1):
    if t[2*n] != a[n]*t[n]: bad += 1; print("T2n", j, n)
  G = lambda n: t[n]
  Gs = [G]
  for k in range(K):
    p, g = PR[k], Gs[-1]
    def h(n, p=p, g=g):
      q, r = divmod(g(p*n), g(n))
      if r: raise ValueError((j, k, n))
      return q
    Gs.append(h)
  for k in range(1, K+1):
    m = 1
    for p in PR[k:]: m *= p
    for n in range(1, NMAX*m//1 + 1):
      try: v = Gs[k](n)
      except ValueError as e: bad += 1; print("nonint", e); continue
      if k == 1 and v != a[n]: bad += 1; print("A", j, n)
print("j=0..12, chain primes", PR, "failures:", bad)
sys.exit(1 if bad else 0)
