# Canonical reduction of (1/sqrt(pi)) (1 - d(u)^n)/u^2 modulo exact derivatives to the
# basis e^{-k u^2} erf(u)^l / u^(l mod 2), k >= 1.  Terms: (a,k,l,p) -> Fraction,
# meaning pi^(p/2) u^a e^{-k u^2} erf(u)^l.
#
from fractions import Fraction as Fr
from collections import defaultdict
import sys
def mul(A,B):
  C=defaultdict(Fr)
  for (a,k,l,p),c in A.items():
    for (b,kk,ll,q),d in B.items():
      C[(a+b,k+kk,l+ll,p+q)]+=c*d
  return {t:c for t,c in C.items() if c!=0}
def start(n):
  N={(0,1,0,0):Fr(1),(0,0,0,0):Fr(-1),(1,0,1,1):Fr(1)}
  Nn={(0,0,0,0):Fr(1)}
  for _ in range(n): Nn=mul(Nn,N)
  T=defaultdict(Fr)
  T[(-2,0,0,-1)]+=1
  for (a,k,l,p),c in Nn.items(): T[(a-2*n-2,k,l,p-1)]-=c
  return {t:c for t,c in T.items() if c!=0}
def canon(T):
  T=defaultdict(Fr,T); bad=[]
  while True:
    todo=[t for t,c in T.items() if c!=0 and not (t[1]>=1 and t[0]==-(t[2]%2))]
    if not todo: return {t:c for t,c in T.items() if c!=0}
    # process the term with the largest |a - target| first
    t=max(todo,key=lambda t:(abs(t[0]+(t[2]%2)), -t[1]))
    a,k,l,p=t; c=T.pop(t)
    if k>=1:
      tg=-(l%2)
      if a>tg:
        T[(a-2,k,l,p)]+=c*Fr(a-1,2*k)
        if l>0: T[(a-1,k+1,l-1,p-1)]+=c*Fr(l,k)
      else:
        T[(a+2,k,l,p)]+=c*Fr(2*k,a+1)
        if l>0: T[(a+1,k+1,l-1,p-1)]-=c*Fr(2*l,a+1)
    else:
      if l==0:
        assert a!=-1, t
        continue
      if a==-1:
        bad.append((t,c)); raise Exception("u^-1 erf^l with k=0: %s"%(t,))
      T[(a+1,1,l-1,p-1)]-=c*Fr(2*l,a+1)
def show(T):
  out=[]
  for (a,k,l,p),c in sorted(T.items(),key=lambda x:(-x[0][2],-x[0][1])):
    out.append("%s*pi^(%d/2)*e^(-%dx^2)*erf^%d/x^%d"%(c,p,k,l,-a))
  return " + ".join(out)
def val0(T):
  # sqrt(pi)*I(0): l=0 terms give c pi^(p/2); l=1 terms give c pi^(p/2) * 2/sqrt(pi)
  v=defaultdict(Fr)
  for (a,k,l,p),c in T.items():
    if l==0: v[p+1]+=c
    elif l==1: v[p]+=2*c
  return {q:x for q,x in v.items() if x!=0}
if __name__=="__main__":
  for n in range(1,int(sys.argv[1])+1):
    T=canon(start(n))
    if n<=4: print("I_%d ="%n, show(T))
    f=Fr(2,3)*Fr(n**3-n**2+2*n+1,2*n+1)
    print(n, val0(T), "conj", f)
