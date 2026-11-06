# The construction of the proof for n >= 1200: e = max(v2(n), v5(n)) trailing zeros,
# P = |H| - 1 swap pairs (v, v+1) above them, one reserved nonzero leading digit,
# subset-sum choice of swaps to reach 0 mod N' (N' = n / 2^a 5^b, H = gcd(9,N') Z/N').
import sys
from math import gcd
sys.set_int_max_str_digits(0)
def v(n,p):
    c=0
    while n%p==0: n//=p; c+=1
    return c
def build(n):
    lo=n*(n-1)//2+1; hi=n*(n+1)//2
    cnt=[0]*10
    for x in range(lo,hi+1):
        for ch in str(x): cnt[int(ch)]+=1
    a,b=v(n,2),v(n,5); e=max(a,b); Np=n//(2**a*5**b)
    h=Np//gcd(9,Np); P=h-1
    c=cnt[:]; c[0]-=e; c[1]-=1          # reserve trailing zeros and leading '1'
    assert c[0]>=0 and c[1]>=0
    pairs=[]
    for vv in (0,2,4,6,8):
        k=min(c[vv],c[vv+1]); pairs+= [(vv,vv+1)]*k
    assert len(pairs)>=P, (n,len(pairs),P)
    pairs=pairs[:P]
    for (x,y) in pairs: c[x]-=1; c[y]-=1
    rest=[d for d in range(10) for _ in range(c[d])]
    # digits from position 0 upward: e zeros, pairs (x at even pos, y at odd pos), rest, leading 1
    low=[0]*e
    pos=e
    base=0; incs=[]
    for (x,y) in pairs:
        # x at pos, y at pos+1 ; swapping adds (x-y)*10^(pos+1) + (y-x)*10^pos = -9*10^pos
        incs.append((-9*pow(10,pos,Np))%Np); pos+=2
    # subset sum DP to find chosen swaps reaching residue
    digits=low[:]
    for (x,y) in pairs: digits+= [x,y]
    digits+= rest+[1]
    V0=sum(d*pow(10,i,Np) for i,d in enumerate(digits))%Np
    target=(-V0)%Np
    reach={0:None}; order=[0]
    for t,inc in enumerate(incs):
        new=[]
        for r in list(reach):
            s=(r+inc)%Np
            if s not in reach: new.append((s,(r,t)))
        for s,pr in new: reach[s]=pr
    assert target in reach, (n,"target not reached")
    chosen=set(); r=target
    while reach[r] is not None:
        r0,t=reach[r]; chosen.add(t); r=r0
    for t in chosen:
        i=e+2*t; digits[i],digits[i+1]=digits[i+1],digits[i]
    s=''.join(map(str,digits[::-1]))
    assert s[0]!='0' and int(s)%n==0
    assert sorted(s)==sorted(''.join(str(x) for x in range(lo,hi+1)))
    return len(pairs)
ns=list(range(1200,1600))+[2000,2310,3003,4096,5005,9999,10010,15015]
for n in ns: build(n)
print("construction verified for",len(ns),"values of n incl. 1200..1599")
