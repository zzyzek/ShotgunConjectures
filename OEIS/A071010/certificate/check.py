# A071010 / A022544: if k is not a sum of two squares then 4 | sigma(k).
# Checks k < 10^6.
#
N = 10**6
s2 = bytearray(N)
a = 0
while a * a < N:
  b = a
  while a*a + b*b < N: s2[a*a + b*b] = 1; b += 1
  a += 1
sig = [0] * N
for d in range(1, N):
  for m in range(d, N, d): sig[m] += d
print("failures:", [k for k in range(1, N) if not s2[k] and sig[k] % 4][:10])
