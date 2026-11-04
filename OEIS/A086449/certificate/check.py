# A086449: a(0)=1, a(2n+1)=a(n), a(2n) = a(n) + sum_{m>=0} a(n-2^m) (a(<0)=0).
# Checks n < 2^16: a(n) odd iff n = 2^k - 1 (then a(n) = 1); a(2^k - 2) = 2^(k-1).
#
N = 1 << 16
a = [1]
for m in range(1, N):
  if m % 2: a.append(a[m//2])
  else:
    n = m // 2; t = a[n]; j = 1
    while n - j >= 0: t += a[n - j]; j *= 2
    a.append(t)
allones = {(1 << k) - 1 for k in range(17)}
print(all((a[n] % 2 == 1) == (n in allones) for n in range(N)) and all(a[n] == 1 for n in allones if n < N)
      and all(a[(1 << k) - 2] == 1 << (k - 1) for k in range(1, 17)))
