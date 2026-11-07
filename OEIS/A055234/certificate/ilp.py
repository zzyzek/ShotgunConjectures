# Find x = prod p^k over chosen items with sigma(x) = n*phi(x): exact ILP over exponent vectors.
import sys, json
import numpy as np
from scipy.optimize import milp, LinearConstraint, Bounds
from sympy import primerange, factorint, totient, divisor_sigma
from fractions import Fraction
d=json.load(open(sys.argv[1])); S=d["S"]; items=[tuple(t) for t in d["items"]]
PS=list(primerange(2,S+1)); idx={p:i for i,p in enumerate(PS)}
def vec(fr):
  v=np.zeros(len(PS))
  for q,e in factorint(fr.numerator).items(): v[idx[q]]+=e
  for q,e in factorint(fr.denominator).items(): v[idx[q]]-=e
  return v
from scipy.sparse import csr_matrix, lil_matrix
from collections import Counter
V=csr_matrix(np.array([vec(Fraction(p**(k+1)-1,(p-1)**2*p**(k-1))) for p,k in items]).T)
mult=Counter(p for p,k in items)
primes=sorted(p for p in mult if mult[p]>1)
G=lil_matrix((max(1,len(primes)),len(items)))
pi={p:i for i,p in enumerate(primes)}
for j,(p,k) in enumerate(items):
  if p in pi: G[pi[p],j]=1
G=G.tocsr()
MINIMISE=True
def solve(n, tl=20):
  t=vec(Fraction(n,1))
  c=np.array([float(np.log(p)*k) for p,k in items]) if MINIMISE else np.zeros(len(items))
  cons=[LinearConstraint(V,t,t), LinearConstraint(G,0,1)]
  r=milp(c,constraints=cons,integrality=np.ones(len(items)),bounds=Bounds(0,1),options={"time_limit":tl})
  if r.x is None: return None, r.status
  x=1
  for j,(p,k) in enumerate(items):
    if r.x[j]>0.5: x*=p**k
  return x, r.status
out=open(sys.argv[3],"a")
for n in [int(a) for a in sys.argv[2].split(",")]:
  x,st=solve(n)
  ok = x is not None and int(divisor_sigma(x))==n*int(totient(x))
  line="n=%d status=%s x=%s verified=%s"%(n,st,x,ok)
  print(line); out.write(line+"\n"); out.flush()
