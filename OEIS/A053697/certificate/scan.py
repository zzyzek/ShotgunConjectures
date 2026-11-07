# For every start 1 <= n < LIM: iterate until the base-11 string matches 1 4* 3 (84)* or 1 5* 4 (84)*.
import re,sys
from sim import step
pat=re.compile(r'^1(4*3|5*4)(84)*$')
D='0123456789A'
def s11(n):
  s=[]
  while n: s.append(D[n%11]); n//=11
  return ''.join(reversed(s))
LIM=int(sys.argv[1]); worst=(0,0); fail=[]
for n0 in range(1,LIM):
  n=n0
  for t in range(3000):
    if pat.match(s11(n)): break
    n=step(n)
  else:
    fail.append(n0); continue
  if t>worst[0]: worst=(t,n0)
print("LIM",LIM,"fail",len(fail),fail[:10],"max steps",worst)
