import numpy as np
N=200000
s=np.zeros(N+1,dtype=np.int64)
for d in range(1,N+1): s[d::d]+=d
defi=np.where(s<2*np.arange(N+1))[0]; defi=defi[defi>0]
isd=np.zeros(N+1,bool); isd[defi]=True
bad=[n for n in range(2,N+1) if not any(isd[a] and isd[n-a] for a in range(1,n//2+1))]
print("n<=%d not sum of two deficient:"%N,bad)
oddab=np.count_nonzero(~isd[1::2][1:]); print("odd abundant <=N:",oddab)
