# Mark-4 by brute force: options of n are n-1, n-2, n-3 (>= 0) and n//4 (n >= 1).
# Compares the P-positions below N with {0} and the numbers of odd 4-adic
# valuation, and with the OEIS data of A171949 and A217319 (fetched 2026-11-06).
#
N = 200000
P = [False] * N
for n in range(N):
  opts = [n - i for i in (1, 2, 3) if n - i >= 0] + ([n // 4] if n >= 1 else [])
  P[n] = not any(P[m] for m in opts)

def v4(n):
  k = 0
  while n % 4 == 0:
    n //= 4
    k += 1
  return k

assert all(P[n] == (n == 0 or v4(n) % 2 == 1) for n in range(N))
a171949 = [0, 4, 8, 12, 20, 24, 28, 36, 40, 44, 52, 56, 60, 64, 68, 72, 76, 84, 88, 92, 100, 104, 108]
assert [n for n in range(110) if P[n]] == a171949
a217319 = [n for n in range(1, 281) if (len(bin(n)) - len(bin(n).rstrip('0'))) % 4 in (2, 3)]
assert a217319 == [n for n in range(1, 281) if P[n]]
print("OK n <", N)
