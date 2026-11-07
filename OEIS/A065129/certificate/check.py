# A065129: if l = A003285(m) (period of the continued fraction of sqrt m) divides m, then l is even or
# all prime factors of l are 1 mod 4 (A004613). Also: every odd m with l | m is in A004613.
# Check for m < LIM; also check odd period => x^2 - m y^2 = -1 (first convergent at end of period).
import sys
from math import isqrt
from sympy import primefactors
LIM=int(sys.argv[1]); cnt=0
def period(m):
  a0=isqrt(m)
  if a0*a0==m: return 0,None
  mm,d,a=0,1,a0; p0,p1=1,a0; q0,q1=0,1; l=0
  while True:
    mm=d*a-mm; d=(m-mm*mm)//d; a=(a0+mm)//d; l+=1
    if a==2*a0: return l,(p1,q1)
    p0,p1=p1,a*p1+p0; q0,q1=q1,a*q1+q0
for m in range(2,LIM):
  l,pq=period(m)
  if l==0: continue
  if l%2==1:
    x,y=pq; assert x*x-m*y*y==-1,m
  if m%l==0:
    cnt+=1
    if l%2==1: assert all(p%4==1 for p in primefactors(l)),(m,l)
    if m%2==1: assert all(p%4==1 for p in primefactors(m)),(m,l)
print("ok m <",LIM,"cases with l | m:",cnt)
