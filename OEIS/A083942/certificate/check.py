# Positions of 1^s 0^s (s = 2^n - 1) among totally balanced numbers (A014486),
# by brute force for n <= 3 and by the Catalan count for n <= 7; compare with data.
from math import comb
def bal(x):
  b = bin(x)[3:] if False else (bin(x)[2:] if x else "")
  h = 0
  for c in b:
    h += 1 if c == '1' else -1
    if h < 0: return False
  return h == 0
cat = lambda k: comb(2*k, k)//(k+1)
data = [0,1,8,625,13402696,19720133460129649,126747521841153485025455279433135688,
  15141471069096667541622192498608408980462133134430650704600552060872705905]
for n in range(0, 4):
  s = 2**n - 1; X = (2**s - 1)*2**s
  assert bal(X)
  assert sum(1 for x in range(X) if bal(x)) == data[n]
for n in range(0, 8):
  assert sum(cat(k) for k in range(1, 2**n)) == data[n]
print("ok")
