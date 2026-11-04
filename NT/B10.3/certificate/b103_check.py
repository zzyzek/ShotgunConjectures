# NT-B10.3 recheck: odd m < 1000 that are not values of
# W(n) = n - d(n) - phi(n) + 1.  W(n) < 1000 forces n <= 1002001
# (argument in the README), so a sieve to N = 1002001 decides every m.
#
N = 1002001
phi = list(range(N+1))
for p in range(2, N+1):
  if phi[p] == p:
    for q in range(p, N+1, p): phi[q] -= phi[q] // p
d = [0]*(N+1)
for a in range(1, N+1):
  for q in range(a, N+1, a): d[q] += 1
vals = set()
big_small = []
for n in range(1, N+1):
  w = n - d[n] - phi[n] + 1
  if w < 1000: vals.add(w)
  if (w < 1000) and (w % 2 == 1) and (n > 2200) : big_small.append(n)
non = [m for m in range(1, 1000, 2) if m not in vals]
print(len(non)); print(non)
print("n > 2200 with odd W < 1000:", big_small[:5], "... count", len(big_small), "max", max(big_small))
