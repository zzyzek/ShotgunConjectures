# Count the interval model for n up to N via column words and block lengths,
# compare with 4n^2-11n+5 and with the b-file.
import sys, itertools
def comps(n,k):
    for cuts in itertools.combinations(range(1,n),k-1):
        b=(0,)+cuts+(n,)
        yield [b[i+1]-b[i] for i in range(k)]
def col(word,lens):
    out=[]
    for c,l in zip(word,lens): out+= [c]*l
    return out
WL=["13","123","143","1243","1423"]; WR=["24","214","234","2134","2314"]
def ok(L,R,n):
    for c in "1234":
        Li=[i for i in range(n) if L[i]==c]; Ri=[i for i in range(n) if R[i]==c]
        if Li and Ri:
            sh=[i for i in Li if i in Ri]
            if not sh: return False
            for i in sh:
                if i not in (Li[0],Li[-1]) or i not in (Ri[0],Ri[-1]): return False
    return True
N=int(sys.argv[1]); bf={int(a):int(b) for a,b in (l.split() for l in open(sys.argv[2]) if l.strip())}
for n in range(2,N+1):
    cs=[ col(w,l) for w in WL for l in comps(n,len(w)) ]
    ds=[ col(w,l) for w in WR for l in comps(n,len(w)) ]
    t=sum(ok(L,R,n) for L in cs for R in ds)
    f=4*n*n-11*n+5
    assert t==bf[n], (n,t,bf[n])
    assert n<3 or t==f
print("ok up to",N)
