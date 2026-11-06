import collections, itertools
exec(open('stat3.py').read().split('cands=')[0])
N=12
data={n:sets(n) for n in range(1,N)}
target={n:{m:coef(m,n) for m in range(1,n+3) if coef(m,n)} for n in range(1,N)}
def feats(S):
  T=set(S); b=blocks(S)
  per=[x for x in S if not(x-1 in T and x+1 in T)]
  return [len(per), len(b), sum(1 for u,v in b if v>u), 1 if 0 in T else 0, len(S), S[-1], S[0], sum(1 for u,v in b if v-u>=2), 1 if (S[-1]-S[0]>0 and b[0][1]>b[0][0]) else 0]
F={n:[feats(S) for S in data[n]] for n in data}
rng=range(-2,3)
for co in itertools.product(rng,repeat=9):
  ok=True
  for n in range(1,N):
    d=collections.Counter(sum(c*f for c,f in zip(co,fs)) for fs in F[n])
    if dict(d)!=target[n]: ok=False; break
  if ok: print("MATCH",co)
print("done")
