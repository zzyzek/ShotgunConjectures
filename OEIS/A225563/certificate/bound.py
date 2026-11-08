# Check sum(totient trajectory of n) <= 3n - 3 for 2 <= n <= N (sieve totients).
# The Lean file proves it for all n; this is only a numerical cross-check.
import sys
N = int(sys.argv[1]); phi = list(range(N + 1))
for p in range(2, N + 1):
    if phi[p] == p:
        for m in range(p, N + 1, p): phi[m] -= phi[m] // p
T = [0, 1] + [0] * (N - 1); worst = 0
for n in range(2, N + 1):
    T[n] = n + T[phi[n]]
    assert T[n] <= 3 * n - 3, n
    worst = max(worst, T[n] / n)
print("N", N, "max sum/n", worst)
