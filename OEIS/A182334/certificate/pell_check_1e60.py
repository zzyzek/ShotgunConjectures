# All triangular numbers T <= 10^60 with T = s^2 +- 1, test the order-9 recurrence.
#
import math
# T(k)=k(k+1)/2 = s^2+-1  <=>  (2k+1)^2 - 8 s^2 = 1 +- 8.  Enumerate via Pell orbits.
sols=set()
for D in (9,-7):
  for x0 in range(1,200):
    r=x0*x0-D
    if r>0 and r%8==0:
      s=math.isqrt(r//8)
      if 8*s*s==r:
        for (x,y) in ((x0,s),(x0,-s)):
          for _ in range(60):
            if x>0 and x%2==1 and x>=3: sols.add((x*x-1)//8)
            x,y=3*x+8*y,x+3*y
sols.add(0)
a=sorted(v for v in sols if 0<=v<10**60)
print(len(a),a[:10],all(a[n]==35*a[n-3]-35*a[n-6]+a[n-9] for n in range(9,len(a))))
oeis=[0,1,3,10,15,120,325,528,4095,11026,17955,139128,374545,609960,4726275,12723490,20720703,160554240,432224101,703893960,5454117903]
print("matches OEIS data:",a[:len(oeis)]==oeis, a[:24])
bad=[n for n in range(9,len(a)) if a[n]!=35*a[n-3]-35*a[n-6]+a[n-9]]
print("recurrence fails at n (0-based):",bad[:10])
