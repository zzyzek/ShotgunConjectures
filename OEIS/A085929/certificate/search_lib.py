from math import isqrt
def pell(D):
  a0=isqrt(D); m,dd,a=0,1,a0; p0,p1=1,a0; q0,q1=0,1
  while True:
    if p1*p1-D*q1*q1==1: return p1,q1
    m=dd*a-m; dd=(D-m*m)//dd; a=(a0+m)//dd
    p0,p1=p1,a*p1+p0; q0,q1=q1,a*q1+q0
