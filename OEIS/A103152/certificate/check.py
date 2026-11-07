# A103152: least odd m with exactly n representations m = 2p + q (p, q odd primes), n = 1..24.
N = 2000
isp = [False, False] + [all(k % d for d in range(2, int(k**0.5) + 1)) for k in range(2, N + 1)]
def reps(m): return sum(1 for p in range(3, m) if isp[p] and p % 2 and m - 2*p >= 3 and (m - 2*p) % 2 and isp[m - 2*p])
first = {}
for m in range(1, N + 1, 2): first.setdefault(reps(m), m)
print([first.get(n) for n in range(1, 25)])
print("a(23) =", first[23], "mod 3 =", first[23] % 3)
