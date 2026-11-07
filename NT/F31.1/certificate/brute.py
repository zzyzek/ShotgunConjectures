# Brute force least m with m, k*m in L (base 4, digits -1,0,1), for cross-checking minm.c.
import sys
def inL(c):
  while c:
    r = c % 4
    if r == 2: return False
    b = {0:0, 1:1, 3:-1}[r]
    c = (c - b)//4
  return True
for k in range(int(sys.argv[1]), int(sys.argv[2])+1, 2):
  m = 1
  while not (inL(m) and inL(k*m)): m += 1
  print(k, m)
