# Checks Shevelev's alternation claim for odd k <= 51 and n < 200000, for both equations
# t(n) = t(n+k) and t(n) + t(n+k) = 1.
N = 200000
t = [bin(n).count('1') % 2 for n in range(N + 60)]
ok = True
for k in range(1, 52, 2):
  for want in (0, 1):
    sol = [n for n in range(N) if (t[n] ^ t[n + k]) == want]
    if any(t[a] == t[b] for a, b in zip(sol, sol[1:])): ok = False; print("fail", k, want)
print("alternation holds for odd k <= 51, n < 200000:", ok)
