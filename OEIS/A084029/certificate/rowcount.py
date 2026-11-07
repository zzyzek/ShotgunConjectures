# A084029: for each n, count n-digit multiples of n with digit sum n (capped), to check the
# conjecture "only one term is zero" (row n has at least n such numbers for n >= 3) for n <= N.
# DP over digits from the most significant: state (value mod n, digit sum so far); counts capped at CAP.
import sys
import numpy as np
N = int(sys.argv[1])
bad = []
for n in range(1, N + 1):
    CAP = n
    # dp[s][r]: number of prefixes with digit sum s and value r mod n (capped)
    dp = np.zeros((n + 1, n), dtype=np.int64)
    for d in range(1, 10):
        if d <= n:
            dp[d][d % n] += 1
    for pos in range(1, n):
        nd = np.zeros_like(dp)
        for d in range(10):
            # new residue (10 r + d) mod n
            idx = (10 * np.arange(n) + d) % n
            for s in range(0, n + 1 - d):
                if dp[s].any():
                    np.add.at(nd[s + d], idx, dp[s])
        dp = np.minimum(nd, CAP)
    c = int(dp[n][0])
    if c < n:
        bad.append((n, c))
print("rows with fewer than n entries, n <=", N, ":", bad)
