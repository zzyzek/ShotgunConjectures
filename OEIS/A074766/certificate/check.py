# A074766: p(2n) - 2 p(n) < 2n.  Direct check for n < 10^6, and the margin of
# the Dusart (1999) bound for n >= 19509:
#   p_k <= k(ln k + ln ln k - 0.9484) (k >= 39017), p_k >= k(ln k + ln ln k - 1) (k >= 2)
#   => (p(2n) - 2p(n))/(2n) <= ln 2 + 0.0516 + ln(1 + ln 2/ln n), decreasing in n.
#
from math import log
N = 2 * 10**6
lim = int(N * (log(N) + log(log(N)))) + 100
s = bytearray([1]) * lim; s[0] = s[1] = 0
for i in range(2, int(lim ** 0.5) + 1):
  if s[i]: s[i*i::i] = bytearray(len(range(i*i, lim, i)))
P = [0]
for i in range(lim):
  if s[i]: P.append(i)
print("direct n < 10^6:", all(P[2*n] - 2*P[n] < 2*n for n in range(1, 10**6)))
n = 19509
print("bound at n = 19509:", log(2) + 0.0516 + log(1 + log(2)/log(n)))
