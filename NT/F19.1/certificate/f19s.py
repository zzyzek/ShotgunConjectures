# For which n is there NO pair of distinct partitions n=a+b+c (0<a<=b<=c) with equal abc?
import sys
N=int(sys.argv[1]); fails=[]
for n in range(3,N+1):
    seen=set(); ok=False
    for a in range(1,n//3+1):
        for b in range(a+1,(n-a+1)//2):
            p=a*b*(n-a-b)
            if p in seen: ok=True;break
            seen.add(p)
        if ok: break
    if not ok: fails.append(n)
print(len(fails),fails[-30:])
