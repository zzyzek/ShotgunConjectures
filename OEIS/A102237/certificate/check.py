# A102237: a(n) = 2^n for n >= 6.  Certificate for the finite parts of the argument.
# (1) explicit representations of 2^n as a sum of n distinct primes, 6 <= n <= 23;
# (2) base case: every even N in [L0, B0] = [ceil(0.9*2^22), 2^23] is a sum of 22 distinct odd primes
#     (the first 20 odd primes 3..73 plus two distinct primes > 73);
# (3) the recurrence L_{k+1} = 2 L_k / (1 - 1/(25 ln^2 L_k)), L_22 = L0, B_k = 2^(k+1):
#     L_k <= 0.95 * 2^k for all k >= 22 (numerically to k = K, analytic tail bound after K).
import math, sys
def sieve(n):
  s = bytearray([1]) * (n + 1); s[0] = s[1] = 0
  for i in range(2, int(n ** 0.5) + 1):
    if s[i]: s[i*i::i] = bytearray(len(s[i*i::i]))
  return s
B0 = 2 ** 23
isp = sieve(B0)
odd_primes = [p for p in range(3, 10000) if isp[p]]
def rep(N, k):
  # N = sum of k distinct odd primes: first k-2 odd primes + p + q, p < q distinct, p, q > q_{k-2}
  small = odd_primes[:k - 2]; R = N - sum(small); lo = small[-1] if small else 2
  p = lo + 1
  while 2 * p < R:
    if isp[p] and isp[R - p]: return small + [p, R - p]
    p += 1
  return None
def rep_search(N, k):
  # backtracking: k distinct odd primes summing to N, largest first
  ps = [p for p in odd_primes if p <= N]
  def go(N, k, maxi):
    if k == 0: return [] if N == 0 else None
    if k == 1:
      return [N] if (N % 2 == 1 and N >= 3 and N <= B0 and isp[N] and (maxi is None or N < maxi)) else None
    for p in reversed([q for q in ps if (maxi is None or q < maxi) and q < N]):
      # remaining k-1 primes are < p: their sum <= sum of the k-1 primes below p
      r = go(N - p, k - 1, p)
      if r is not None: return [p] + r
      if sum(q for q in ps if q < p)  < N - p: break
    return None
  return go(N, k, None)
# (1)
for n in range(6, 24):
  T = 2 ** n
  if n % 2 == 0: r = rep(T, n) or rep_search(T, n)
  else:
    r = rep(T - 2, n - 1) or rep_search(T - 2, n - 1)
    r = [2] + r if r else None
  assert r and len(r) == n and len(set(r)) == n and sum(r) == T and all(isp[x] for x in r), n
  print(n, r[-4:] if n > 12 else r)
# (2)
L0 = math.ceil(0.9 * 2 ** 22); L0 += L0 % 2
bad = [N for N in range(L0, B0 + 1, 2) if rep(N, 22) is None]
assert not bad, bad[:5]
print("base: every even N in [%d, %d] is a sum of 22 distinct odd primes" % (L0, B0))
# (3)  track r_k = L_k / 2^k; ln L_k = ln r_k + k ln 2
r = L0 / 2 ** 22; K = 100000
for k in range(22, K):
  lnL = math.log(r) + k * math.log(2)
  assert lnL - math.log(2) >= math.log(396738)
  assert r <= 0.95, k
  r = r / (1 - 1 / (25 * lnL ** 2))
a = math.log(r) + K * math.log(2)
tail = (1 / a ** 2 + 1 / (a * math.log(2))) / 25 * 1.01
print("L_k/2^k <= 0.95 for 22 <= k < %d; r_K = %.6f; tail factor exp(%.2e); limit bound %.6f" % (K, r, tail, r * math.exp(tail)))
assert r * math.exp(tail) <= 0.95
