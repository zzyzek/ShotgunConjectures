import sys, numpy as np
from scipy.optimize import milp, LinearConstraint, Bounds
from scipy.sparse import lil_matrix
def best(x):
  pairs=[(a,b) for a in range(1,x+1) for b in range(2*a,x+1,a)]
  A=lil_matrix((len(pairs),x))
  for r,(a,b) in enumerate(pairs): A[r,a-1]=1; A[r,b-1]=1
  c=-np.array([x+1-a for a in range(1,x+1)],float)
  res=milp(c,constraints=LinearConstraint(A.tocsr(),-np.inf,1),integrality=np.ones(x),bounds=Bounds(0,1))
  z=np.round(res.x).astype(int)
  return int(round(-res.fun)), [a for a in range(1,x+1) if z[a-1]]
for x in [int(t) for t in sys.argv[1:]]:
  v,S=best(x)
  cand=sum(x+1-a for a in range(1,x+1) if 3*a> x and 3*a<=2*x)
  print(x, v, cand, v-cand, round(v-x*x/6,1), S if x<=40 else (min(S),max(S),len(S)))
