# A056142: a(n) = concatenation of n, n//10, n//100, ... (nonzero ones).
# 1. Data terms and brute force: all n < 10^6 with a(n) a palindrome.
# 2. Fixed-point word X over {a, b}: X = R_1 R_2 ..., R_m = reverse(X[1..m]),
#    X_1 = a, X_2 = b. By the reduction (Lean: word_reduction), a d-digit n
#    with a(n) a palindrome and x_1 != x_2 has digit word = image of X[1..d].
#    Check that W(X[1..d]) is not a palindrome for 4 <= d <= D, using the
#    necessary condition X[d+1..2d-1] = X[1..d-1] (block u_{d-1} of W).
#
import sys

def a(n):
  s = ''
  while n > 0:
    s += str(n); n //= 10
  return int(s) if s else 0

data = [0,1,2,3,4,5,6,7,8,9,101,111,121,131,141,151,161,171,181,191,202,212,
        222,232,242,252,262,272,282,292,303,313,323,333,343,353,363,373,383,
        393,404,414,424,434,444,454,464,474,484,494,505,515,525,535,545,555]
assert [a(n) for n in range(len(data))] == data
pal = lambda m: str(m) == str(m)[::-1]
for n in range(100, 10**6):
  if pal(a(n)):
    if len(str(n)) == 3:
      assert pal(n)
    else:
      assert len(set(str(n))) == 1, n
print("brute force n < 10^6: 3 digits <-> n palindrome; 4..6 digits -> all digits equal")

D = int(sys.argv[1]) if len(sys.argv) > 1 else 400000
N = 2*D + 2
x = [None, 0, 1]
m = 2
for p in range(3, N + 1):
  while m*(m+1)//2 < p: m += 1
  x.append(x[m*(m+1)//2 - p + 1])
X = x[1:]
def W(s):
  return [c for k in range(len(s), 0, -1) for c in s[:k]]
for d in range(4, 41):
  w = W(X[:d]); assert w != w[::-1]
mx = 0
for d in range(4, D + 1):
  i = 1
  while X[d+i-1] == X[i-1]: i += 1
  assert i <= d - 1, d
  mx = max(mx, i)
print("X: W(X[1..d]) not a palindrome for 4 <= d <= %d (max first-mismatch offset in block u_{d-1}: %d)" % (D, mx))
