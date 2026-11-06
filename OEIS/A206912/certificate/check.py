# A206912(n) = n + #{k >= 1 : H_k < log(n+1)} (position of log(n+1) among
# the harmonic partial sums jointly ranked with {log(j+1)}).
# Checks: differences are 1 or 2 for n < N; the complement of the first
# values agrees with the A206911 data (OEIS, cached 2026-11-05).
#
import math

N = 20000
A206911_DATA = [2,5,8,11,13,16,19,22,24,27,30,33,36,38,41,44,47,49,52,55,58,
                61,63,66,69,72,74,77,80,83,86,88,91,94,97,100,102,105,108,
                111,113,116,119,122,125,127,130,133,136,138,141]

H = [0.0]
for k in range(1, N + 2):
  H.append(H[-1] + 1.0 / k)

a = []
k = 0
for n in range(1, N + 1):
  L = math.log(n + 1)
  while (k + 1 <= N) and (H[k + 1] < L):
    k += 1
  a.append(n + k)

d = [a[i + 1] - a[i] for i in range(len(a) - 1)]
assert set(d) <= {1, 2}, "difference outside {1,2}"

top  = A206911_DATA[-1]
comp = [x for x in range(1, top + 1) if x not in set(a)]
assert comp == A206911_DATA, (comp, A206911_DATA)
print("A206912 first terms:", a[:20])
print("differences in {1,2} for n <", N, "; counts:", d.count(1), d.count(2))
print("complement matches A206911 data up to", top)
