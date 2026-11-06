# For each n < N, find an arrangement of the digits of T(n-1)+1..T(n) (no leading zero)
# that is divisible by n. Random shuffles, residue by dot product with 10^i mod n.
import numpy as np, sys, random
sys.set_int_max_str_digits(0)
N=int(sys.argv[1]); rng=np.random.default_rng(1)
worst=0
for n in range(1,N):
    lo=n*(n-1)//2+1; hi=n*(n+1)//2
    digs=np.array([int(c) for x in range(lo,hi+1) for c in str(x)],dtype=np.int64)
    D=len(digs)
    p10=np.ones(D,dtype=np.int64)
    for i in range(1,D): p10[i]=(p10[i-1]*10)%n
    tries=0
    while True:
        tries+=1
        perm=rng.permutation(digs)
        if perm[-1]==0:   # index D-1 is the leading digit (highest power)
            nz=np.nonzero(perm)[0]; j=nz[0]; perm[-1],perm[j]=perm[j],perm[-1]
        if int(np.dot(perm,p10)%n)==0:
            # verify exactly with Python big int
            s=''.join(map(str,perm[::-1]))
            assert s[0]!='0' and int(s)%n==0 and sorted(s)==sorted(''.join(str(x) for x in range(lo,hi+1)))
            break
        if tries>200*n+1000: print("FAIL",n); sys.exit(1)
    worst=max(worst,tries/n)
    if n%100==0: print(n,"ok, max tries/n so far",round(worst,2),flush=True)
print("all n <",N,"ok")
