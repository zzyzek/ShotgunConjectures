from functools import lru_cache
@lru_cache(None)
def nmul(a,b):
    if a<2 or b<2: return a*b
    # split at largest Fermat 2-power F with F <= max(a,b)
    m=max(a,b); k=0
    while (1<<(1<<(k+1)))<=m: k+=1
    h=1<<k; F=1<<h
    a1,a0=a>>h,a&(F-1); b1,b0=b>>h,b&(F-1)
    c11=nmul(a1,b1); c00=nmul(a0,b0)
    c=nmul(a1^a0,b1^b0)^c00   # a1b0+a0b1+a1b1
    # x^2 = x + F/2 (as F*F = F + F/2 in nim) -> a1b1 x^2 = a1b1 x + a1b1*(F/2)
    hi=c
    lo=c00^nmul(c11,F>>1)
    return (hi<<h)^lo
# check sesquimultiple squares
bad=[m for m in range(1,64) if nmul(1<<m,1<<m)!=3<<(m-1)]
print("2^m squares bad:",bad)
# check conjectures directly for small n
def fact(N):
    r=1
    for i in range(1,N+1): r=nmul(r,i)
    return r
print([fact(2**n-1) for n in range(1,14)])
print([fact(2**n+2**(n-1)-1) for n in range(1,14)])
data=[1,2,1,4,2,11,1,8,5,9,2,4,9,4,1,16,8,140,5,82,9,145,2,44,6,108,9,154,13,209,1,32,20,132,10,243,172,123,4,139,68,62,11,222,182,92,2,16,36,224,5,242,91,24,11,105,178,56,5,241,92,205,1,64,39,20,23,161,225,53]
r=1; out=[]
for i in range(1,len(data)+1): r=nmul(r,i); out.append(r)
print("data match:",out==data)
def npow(a,e):
    r=1
    while e:
        if e&1: r=nmul(r,a)
        a=nmul(a,a); e>>=1
    return r
for k in range(1,6):
    xk=1<<(1<<k); xk1=1<<(1<<(k-1)); qp=1<<(1<<(k-1))
    s=npow(xk,qp)^xk
    print(k, "s=",s,"s^x_{k-1}=",s^xk1, "< 2^(2^(k-1)-1)?", (s^xk1) < (1<<((1<<(k-1))-1)))
