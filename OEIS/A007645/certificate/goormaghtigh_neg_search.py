# Search (n^q-1)/(n-1) = (b^r+1)/(b+1) <= X with n, b >= 2 and odd q, r >= 5.
# Prints every common value, whether it is prime and whether it is c^2+c+1.
import sys, math
X = 10 ** int(sys.argv[1])
def rep_minus(X):
  S = {}
  q = 5
  while 2 ** (q - 1) <= X:
    n = 2
    while True:
      v = (n ** q - 1) // (n - 1)
      if v > X: break
      S.setdefault(v, []).append((n, q)); n += 1
    q += 2
  return S
def rep_plus(X, S):
  out = []
  r = 5
  while 2 ** (r - 1) // 3 <= X:
    b = 2
    while True:
      v = (b ** r + 1) // (b + 1)
      if v > X: break
      if v in S: out.append((v, S[v], (b, r)))
      b += 1
    r += 2
  return out
def isprime(v):
  if v < 2: return False
  for d in (2,3,5,7,11,13,17,19,23,29,31,37):
    if v % d == 0: return v == d
  dd, s = v - 1, 0
  while dd % 2 == 0: dd //= 2; s += 1
  for a in (2,3,5,7,11,13,17,19,23,29,31,37,41):
    x = pow(a, dd, v)
    if x in (1, v - 1): continue
    for _ in range(s - 1):
      x = x * x % v
      if x == v - 1: break
    else: return False
  return True
def is_c2c1(v):
  c = (math.isqrt(4 * v - 3) - 1) // 2
  return c * c + c + 1 == v
S = rep_minus(X)
print("X = 10^%s, |S| = %d" % (sys.argv[1], len(S)))
for v, a, b in rep_plus(X, S):
  print(v, a, b, "prime" if isprime(v) else "composite", "c^2+c+1" if is_c2c1(v) else "")
print("done")
