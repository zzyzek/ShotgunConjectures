# A081086: a(k+1) = least a with sum_{j=1}^{k+1} [0; a_j, ..., a_k, a] < 1  (reproduces the OEIS data).
# r_k = 1 - sum_{j<=k} [0; a_j, ..., a_k] is the deficit; a(k+1) is about 1/r_k.
# Prints D_k = ln(a_{k+1}) - 2 ln(a_k) and the log ratio.
import sys
sys.set_int_max_str_digits(0)
from fractions import Fraction as F
from math import log
K=int(sys.argv[1])
data=[2,2,9,91,14201,252238179,82413709268226496,12393783734739289765092773334814410,940449499772176767594719706273493318801155215211368219531441729200804]
def ln(z):
    s=str(z) if z<10**4000 else None
    if s is None:
        b=z.bit_length(); return (b-60)*log(2)+log(z>>(b-60))
    return log(z) if z<10**300 else len(s)*log(10)+log(int(s[:15])/10**(15-1))-log(10)
A=[]
def s(a):
    x=F(1,a); tot=x
    for aj in reversed(A):
        x=1/(aj+x); tot+=x
    return tot
for k in range(K):
    if A:
        x=F(1,A[-1]); tot=x
        for aj in reversed(A[:-1]):
            x=1/(aj+x); tot+=x
        r=1-tot; assert r>0
        a0=max(1,int(1/r))
    else:
        a0=1
    a=a0+3
    while s(a)>=1: a+=1
    lo=a-1; step=1
    while lo>=1 and s(lo)<1: lo=max(0,a-step); step*=2
    hi=a
    while hi-lo>1:
        mid=(lo+hi)//2
        if mid>=1 and s(mid)<1: hi=mid
        else: lo=mid
    a=hi
    assert s(a)<1 and (a==1 or s(a-1)>=1)
    A.append(a)
    msg=f"{k+1} a0-a={a0-a} digits={len(str(a)) if a<10**4000 else 'many'}"
    if k<len(data): msg+=" data_ok" if data[k]==a else " DATA_MISMATCH"
    if k>=1:
        msg+=f" D=ln(a/a_prev^2)={ln(a)-2*ln(A[-2]):.4f} logratio={ln(a)/ln(A[-2]) if A[-2]>1 else 0:.6f} a>=a_prev(a_prev-1):{a>=A[-2]*(A[-2]-1)}"
    print(msg,flush=True)
open('A081086_terms.txt','w').write('\n'.join(map(str,A))+'\n')
