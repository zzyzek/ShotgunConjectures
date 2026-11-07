# DIMACS CNF: exists completely additive f: {1..N} -> Z/K with no r, r+2 <= N, f(r)=f(r+1)=f(r+2)=0?
# Variables y[n][v] (f(n) = v) for 2 <= n <= N, exactly-one per n; f(1) = 0.
# Composite n = p*m (p = least prime factor): y[p][a] & y[m][b] -> y[n][(a+b)%K].
# Optional symmetry breaking: none (the K-1 automorphisms v -> c*v, c a unit, could fix one prime).
import sys
N = int(sys.argv[1]); K = int(sys.argv[2]) if len(sys.argv) > 2 else 5
sym = (len(sys.argv) > 3 and sys.argv[3] == 'sym')
spf = list(range(N+1))
for i in range(2, int(N**0.5)+1):
  if spf[i] == i:
    for j in range(i*i, N+1, i):
      if spf[j] == j: spf[j] = i
def var(n, v): return (n-2)*K + v + 1
clauses = []
for n in range(2, N+1):
  clauses.append([var(n, v) for v in range(K)])
  for a in range(K):
    for b in range(a+1, K):
      clauses.append([-var(n, a), -var(n, b)])
  p = spf[n]
  if p != n:
    m = n // p
    for a in range(K):
      for b in range(K):
        if m == 1: continue
        clauses.append([-var(p, a), -var(m, b), var(n, (a+b) % K)])
def zero(n):
  return None if n == 1 else var(n, 0)
for r in range(1, N-1):
  lits = [zero(x) for x in (r, r+1, r+2)]
  clauses.append([-l for l in lits if l is not None])
if sym:
  # f(2) in {0, 1}: any assignment can be scaled by a unit c of Z/K (c*f is additive too and
  # has the same zero set), so f(2) != 0 can be normalised to 1.
  clauses.append([var(2, 0), var(2, 1)])
out = sys.stdout
out.write('p cnf %d %d\n' % ((N-1)*K, len(clauses)))
for c in clauses:
  out.write(' '.join(map(str, c)) + ' 0\n')
