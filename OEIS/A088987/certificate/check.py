# A088982 / A088987: primes strictly between prime(p_x) and prime(p_{x+1}) number
# p_{x+1} - p_x - 1: at least 1 and odd for x >= 2, zero for x = 1 (between 3 and 5).
#
N = 10**6
s = bytearray([1]) * N; s[0] = s[1] = 0
for i in range(2, 1001):
  if s[i]: s[i*i::i] = bytearray(len(range(i*i, N, i)))
pr = [i for i in range(N) if s[i]]
pip = [pr[p - 1] for p in pr if p - 1 < len(pr)]
cnt = [sum(s[pip[i] + 1: pip[i+1]]) for i in range(len(pip) - 1)]
print("x = 1 count:", cnt[0], " x >= 2 all odd and >= 1:", all(c % 2 == 1 for c in cnt[1:]), " pairs:", len(cnt))
