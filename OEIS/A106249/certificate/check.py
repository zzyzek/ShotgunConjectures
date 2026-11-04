# A106249: coefficients of (1-x+x^2+x^3)/((1+x)(1+x^2)(1-x)^2) versus the number of
# roots of x^m + 1 with negative real part (numerically), for m = n and m = n + 1.
import cmath, math
N = 200
num = [1, -1, 1, 1]; den = [1, -1, 0, 0, -1, 1]   # (1+x)(1+x^2)(1-x)^2 = 1 - x - x^4 + x^5
a = []
for n in range(N):
  a.append((num[n] if n < 4 else 0) - sum(den[i] * a[n - i] for i in range(1, min(n, 5) + 1)))
def roots_left(m): return sum(1 for k in range(m) if math.cos(math.pi * (2*k + 1) / m) < -1e-12)
print("a(n) = #roots of x^(n+1)+1 in Re<0, n < 200:", all(a[n] == roots_left(n + 1) for n in range(N)))
print("a(1) =", a[1], "but x^1 + 1 has", roots_left(1), "root in Re < 0")
