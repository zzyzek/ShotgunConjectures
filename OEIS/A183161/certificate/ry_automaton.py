# Exact Z/4 Rowland-Yassawi system: basis (1, W), W = sum_{m>=1, v2(m) even} t^m,
# (1-t) W = t - (1-t) sigma(W). Q = (1-t)((1-t)^2 - x), U = Q^2, M = Q^2.
# state (N0,N1) means (N0 + N1 W)/Q^2 ; step r: N0' = cart(N0 M + N1 * c10), N1' = cart(N1 * c11)
# with M*W = c10*sigma(1) + c11*sigma(W): c10 = Q^2 t/(1-t), c11 = -Q^2.
import sys
from math import comb
c=int(sys.argv[1])
def mul(A,B):
    C={}
    for (a,b),u in A.items():
        for (d,e),v in B.items():
            k=(a+d,b+e); C[k]=(C.get(k,0)+u*v)%4
    return {k:v for k,v in C.items() if v}
def add(*As):
    C={}
    for A in As:
        for k,v in A.items(): C[k]=(C.get(k,0)+v)%4
    return {k:v for k,v in C.items() if v}
def sc(s,A): return {k:(s*v)%4 for k,v in A.items() if (s*v)%4}
def lam(A,r): return {((a-r)//2,(b-r)//2):v for (a,b),v in A.items() if a%2==r and b%2==r}
def sig(A): return {(2*a,2*b):v for (a,b),v in A.items()}
def pw(A,k):
    R={(0,0):1}
    for _ in range(k): R=mul(R,A)
    return R
omt={(0,0):1,(0,1):3}
B=add(pw(omt,2),{(1,0):3})
Q=mul(omt,B); Q2=pw(Q,2)
assert pw(Q2,2)==sig(Q2)
c10=mul({(0,1):1},mul(omt,pw(B,2)))   # Q^2 t/(1-t) = t (1-t) B^2
c11=sc(3,Q2)
def step(st,r):
    N0,N1=st
    return (lam(add(mul(N0,Q2),mul(N1,c10)),r), lam(mul(N1,c11),r))
def key(st): return (tuple(sorted(st[0].items())),tuple(sorted(st[1].items())))
N0=mul(pw(omt,2-c),Q)
init=(N0,sc(2,N0))
states={key(init):0}; order=[init]; trans=[]
i=0
while i<len(order):
    tr=[]
    for r in (0,1):
        s2=step(order[i],r); k=key(s2)
        if k not in states: states[k]=len(order); order.append(s2)
        tr.append(states[k])
    trans.append(tr); i+=1
print("states",len(order),trans)
for s in order: print(s)
out=[s[0].get((0,0),0)%4 for s in order]  # Q(0,0)=1, W(0)=0
print("out",out)
def run(n):
    s=0
    while n: s=trans[s][n&1]; n>>=1
    return out[s]
def T(n): return sum(comb(n,2*k)*comb(2*k,k) for k in range(n//2+1))
def a(n):
    if n==0: return 1
    if c==0: return sum(T(k)*comb(3*n-k,n-k)*2*k//(3*n-k) for k in range(n+1))
    return sum(T(k)*comb(3*n-k+1,n-k)*(2*k+1)//(3*n-k+1) for k in range(n+1))
print("mismatch",[n for n in range(400) if run(n)!=a(n)%4][:5])
def lit(d):
    if not d: return "[]"
    mi=max(a for a,b in d)
    rows=[]
    for i in range(mi+1):
        js=[b for a,b in d if a==i]
        row=[d.get((i,j),0) for j in range(max(js)+1)] if js else []
        rows.append("["+", ".join(map(str,row))+"]")
    return "["+", ".join(rows)+"]"
if c==0:
    for k,s in enumerate(order): print(f"  ({lit(s[0])},\n   {lit(s[1])}),")
