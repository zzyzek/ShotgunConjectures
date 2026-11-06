# Compute A081847 greedily (a(1)=1, least positive y with concat(a(n-1),y) a new triangular
# number) and A082235(n) = concat(a(n), a(n+1)); compare with the OEIS data and list small
# triangular numbers that never occur. Usage: python3 check.py [terms]
import sys
from math import isqrt
def tri(t): m=(isqrt(8*t+1)-1)//2; return m*(m+1)//2==t
N=int(sys.argv[1]) if len(sys.argv)>1 else 400
a=[1]; seen=set(); b=[]
for n in range(2,N+1):
  y=1
  while True:
    v=int(str(a[-1])+str(y))
    if tri(v) and v not in seen: break
    y+=1
  seen.add(v); b.append(v); a.append(y)
A=[1,5,5,28,50,50,403,651,511,566,16,53,56,1,20,16,110,26,28,203,203,841,753,378,885,115,440,391,6,6,30,81,28,441,330,891,1,36,55,65,55,278,631,90,3,6,66,70,3,25,3,51,51,360,46,5,95,91,80,200,661,825,6,105,85]
assert a[:len(A)]==A, "A081847 data mismatch"
assert b[:5]==[15,55,528,2850,5050]
print("A081847 data matches; last digits of a(n), n>=2:",sorted({x%10 for x in a[1:]}))
print("triangular numbers <= 200 not hit in",N,"terms:",[t for t in range(1,201) if tri(t) and t not in seen])
