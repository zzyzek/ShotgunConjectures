# A000040 (wiki conjecture list): for n > 2, p = prime(n),
# p == (6 f + (-1)^f - 3)/2 with f = floor(p/3) + 1.
# Checks every prime 5 <= p < 10^6.
#
def primes(N):
  s = bytearray([1]) * N; s[0] = s[1] = 0
  for i in range(2, int(N ** 0.5) + 1):
    if s[i]: s[i*i::i] = bytearray(len(range(i*i, N, i)))
  return [i for i in range(N) if s[i]]

bad = [p for p in primes(10**6) if p >= 5 and (6*(p//3 + 1) + (-1)**(p//3 + 1) - 3)//2 != p]
print("failures:", bad)
