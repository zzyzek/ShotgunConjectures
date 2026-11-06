# Check the census by column words against the family counts of the proof,
# using the brute-force solutions of brute.py (n = 3..7).
from brute import sols
from collections import Counter
from math import comb
def words(g):
    wl=[];wr=[]
    for r in g:
        if not wl or wl[-1]!=r[0]: wl.append(r[0])
        if not wr or wr[-1]!=r[1]: wr.append(r[1])
    return (''.join(map(str,wl)),''.join(map(str,wr)))
for n in range(3,8):
    C=Counter(words(g) for g in sols(n))
    want={('13','24'):(n-1)**2,
          ('123','24'):comb(n-1,2),('143','24'):comb(n-1,2),
          ('13','214'):comb(n-1,2),('13','234'):comb(n-1,2),
          ('123','234'):comb(n-2,2),('143','214'):comb(n-2,2),
          ('1243','24'):n-3,('13','2134'):n-3}
    want={k:v for k,v in want.items() if v}
    assert dict(C)==want,(n,C)
    assert sum(C.values())==4*n*n-11*n+5
    print(n,"families ok",sum(C.values()))
