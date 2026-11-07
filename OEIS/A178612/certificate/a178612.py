from math import isqrt
c=0
for p in range(-300,301):
    if p==0: continue
    for q in range(-3000,3001):
        if q==0: continue
        v=p**6-4*p**4*q+4*p**2*q**2+4*q**3
        if v>0:
            r=isqrt(v)
            if r*r==v: print("square",p,q,v); c+=1
print("squares found:",c)
