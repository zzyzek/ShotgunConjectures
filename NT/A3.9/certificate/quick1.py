import sys
from sympy import isprime, totient, divisors, factorint, primerange
from math import isqrt
# 1. A12.1: is (1093*3511)^2 a base-2 psp?
m=1093*3511; print("A12.1 (1093*3511)^2 psp2:", pow(2,m*m-1,m*m)==1)
# 2. Finucane: preimages under phi(n)+1 ending at 5,7 (n up to 10^4 suffices since phi(n)+1<n, and phi(n)>=sqrt(n/2))
def endp(n):
    while not (n<=2 or isprime(n)): n=totient(n)+1
    return n
print("B41.5 ->5:",[n for n in range(1,3000) if endp(n)==5]," ->7:",[n for n in range(1,3000) if endp(n)==7])
# 3. B16.6 AAC for non-prime d: Pell t^2-d u^2=1 fundamental, d | u ?
def pell(d):
    a0=isqrt(d); m,dd,a=0,1,a0; p0,p1=1,a0; q0,q1=0,1
    while p1*p1-d*q1*q1!=1:
        m=dd*a-m; dd=(d-m*m)//dd; a=(a0+m)//dd
        p0,p1=p1,a*p1+p0; q0,q1=q1,a*q1+q0
    return p1,q1
def fundunit(d):
    # fundamental unit of Q(sqrt d) for squarefree d: smallest (t+u sqrt d)/2 or t+u sqrt d with norm +-1
    best=None
    for u in range(1,10**6):
        for s in (-4,4):
            t2=d*u*u+s
            if t2>0:
                t=isqrt(t2)
                if t*t==t2: return (t,u,2)  # (t+u sqrt d)/2 with t^2-du^2=+-4
    return None
pellc=[d for d in range(2,430+1) if isqrt(d)**2!=d and not isprime(d) and pell(d)[1]%d==0]
print("B16.6 Pell u divisible by d, d nonsquare composite <=430:",pellc)
sqf=lambda d: all(e==1 for e in factorint(d).values())
print("   squarefree subset:",[d for d in pellc if sqf(d)])
# 4. A3.9 smallest prime with digit sum k
def smallest_prime_digitsum(k):
    # enumerate numbers with digit sum k in increasing order by length then lexicographic
    from itertools import count
    L=(k+8)//9
    while True:
        # generate in increasing order: recursive smallest-first
        def gen(pos,rem,first):
            if pos==L:
                if rem==0: yield ''
                return
            lo=1 if first else 0
            for dgt in range(lo,10):
                r=rem-dgt
                if 0<=r<=9*(L-pos-1):
                    for tail in gen(pos+1,r,False): yield str(dgt)+tail
        for s in gen(0,k,True):
            n=int(s)
            if isprime(n): return n
        L+=1
bad=[]
res={}
for k in range(2,180):
    if k%3==0: continue
    p=smallest_prime_digitsum(k); res[k]=p
    if k>25 and p%10!=9: bad.append((k,'mod10',p))
    if k>38 and p%100!=99: bad.append((k,'mod100',p))
    if k>59 and p%1000!=999: bad.append((k,'mod1000',p))
print("A3.9 violations k<180:",bad[:20])
