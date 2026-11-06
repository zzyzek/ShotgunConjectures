from collections import Counter
def a(n): return n*(2*n*n+6*n-5)//3
for n in range(1, 13):
  S = Counter(y + z for y in range(1, n+1) for z in range(1, n+1))
  c = sum(v * S.get(s - 2, 0) for s, v in S.items())
  print(n, c, [a(n+s) if n+s>=1 else None for s in (-2,-1,0)])
