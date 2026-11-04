# A145878: T(n,k) by T(n,k) = sum_{i=1..n-k+1} T(n-i,k-1)*T(i-1,0),
# T(n,0) = A052186(n) (computed as n! minus the k >= 1 entries).
# Check the five polynomial formulas for k <= 60.
#
from math import factorial
N = 70
T = [[0] * (N + 1) for _ in range(N + 1)]
for n in range(N + 1):
  for k in range(1, n + 1):
    T[n][k] = sum(T[n - i][k - 1] * T[i - 1][0] for i in range(1, n - k + 2))
  T[n][0] = factorial(n) - sum(T[n][1:n + 1])
F = {3: lambda k: 3*k + 3, 4: lambda k: (k+1)*(k+28)//2, 5: lambda k: (k+1)*(3*k+77),
     6: lambda k: (k+1)*(k*k+110*k+2982)//6, 7: lambda k: (k+1)*(3*k*k+235*k+7352)//2}
print("T(n,0), n<8:", [T[n][0] for n in range(8)])
print("formulas hold for k <= 60:", all(T[r+k][k] == F[r](k) for r in F for k in range(0, 61)))
