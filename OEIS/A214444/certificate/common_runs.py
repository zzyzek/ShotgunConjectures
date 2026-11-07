# Longest run of equal lengths a(n+i) = b(n+x+i) over all shifts, first N blocks of each chain.
from sympy import isprime
def S(e): return e*(e+1)*(2*e+1)//6
def nxt(s):
    L=1
    while True:
        L+=1
        tot=S(s+L-1)-S(s-1)
        if tot%L==0 and isprime(tot//L): return L
def chain(s,N):
    out=[]
    for _ in range(N):
        L=nxt(s); out.append(L); s+=L
    return out
N=20000
a=chain(0,N); b=chain(1,N)
best=(0,None)
for W in range(2,40):
    hb={}
    for j in range(N-W): hb.setdefault(tuple(b[j:j+W]),[]).append(j)
    found=[(i,hb[tuple(a[i:i+W])]) for i in range(N-W) if tuple(a[i:i+W]) in hb]
    if not found: print("longest common run length",W-1); break
    best=(W,found[:3])
print(best)
