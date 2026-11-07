# All consecutive pairs (x, x+1) of powerful numbers with x+1 <= N (N = 10^15 default); prints pairs whose
# prime signatures agree, and the signature counts. Powerful n = a^2 b^3 (b squarefree), unique.
import sys, numpy as np
from math import isqrt
from sympy import factorint
N=int(float(sys.argv[1]))
B=int(round(N**(1/3)))+2
sf=np.ones(B+1,dtype=bool); sf[0]=False
for p in range(2,isqrt(B)+1): sf[p*p::p*p]=False
chunks=[]
for b in range(1,B+1):
  if not sf[b]: continue
  b3=b**3
  if b3>N: break
  amax=isqrt(N//b3)
  a=np.arange(1,amax+1,dtype=np.int64)
  chunks.append(a*a*b3)
v=np.concatenate(chunks); del chunks
v.sort()
idx=np.nonzero(np.diff(v)==1)[0]
print("powerful numbers <=N:",len(v),"consecutive pairs:",len(idx),flush=True)
from collections import Counter
same=Counter(); allsig=Counter()
def sig(n): return tuple(sorted(factorint(n).values()))
for i in idx:
  x=int(v[i]); s1=sig(x); s2=sig(x+1)
  if s1==s2:
    same[s1]+=1
    if same[s1]<=2: print("SAME",x,x+1,s1,factorint(x),factorint(x+1),flush=True)
print("signatures realised by consecutive powerful pairs:",dict(same))
