import sys
from sympy import prime
data=[0,0,1,1,0,0,1,1,2,4,9,14,21,46,112,204,374,809,1586,3237,6385,12539,25637,50603,100891,20382,40281]
for n in range(23,28):
    s=open(f"F{n}.txt").read().strip(); p=str(prime(n))
    ov=sum(1 for i in range(len(s)-len(p)+1) if s.startswith(p,i)) if len(s)<3000000 else None
    if ov is None:
        import re; ov=len(re.findall('(?='+p+')',s))
    no=s.count(p)
    print(n,p,len(s),ov,no,data[n-1], 'OK' if data[n-1] in (ov,no) else 'MISMATCH',flush=True)
