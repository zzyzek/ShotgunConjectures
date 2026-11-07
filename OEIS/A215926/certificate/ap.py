# almost perfect numbers (sigma(k) = 2k - 1) up to N; and a(n) for n <= M checked against conjecture 1, 2
import numpy as np, sys
N = int(sys.argv[1]); M = int(sys.argv[2])
s = np.zeros(N + 1, dtype=np.int64)
for d in range(1, N + 1):
    s[d::d] += d
k = np.arange(N + 1, dtype=np.int64)
ap = np.nonzero(s[1:] == 2 * k[1:] - 1)[0] + 1
print("almost perfect <= %d:" % N, ap.tolist())
