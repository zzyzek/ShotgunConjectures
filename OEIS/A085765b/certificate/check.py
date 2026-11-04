# A086450: a(0)=1, a(2n+1)=a(n), a(2n)=sum_{j<=n} a(j) (n >= 1).
# A085765(n) = A086450(2n).  Checks the mod-2 patterns for n < 20000.
#
N = 40000
a = [1]; S = [1]
for m in range(1, N):
  a.append(a[m//2] if m % 2 else S[m//2]); S.append(S[-1] + a[-1])
P = [1, 1, 0, 1, 0, 0, 1]
print("A086450 mod 2 = 1,1,0,1,0,0,1 repeating:", all(a[n] % 2 == P[n % 7] for n in range(N)))
Q = [0, 0, 1, 1, 1, 0, 1]
print("A085765 mod 2 = 0,0,1,1,1,0,1 repeating from n = 1:", all(a[2*n] % 2 == Q[(n - 1) % 7] for n in range(1, N//2)))
