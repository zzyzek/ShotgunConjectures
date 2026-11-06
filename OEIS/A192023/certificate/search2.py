from collections import Counter
def a(n): return n*(2*n*n+6*n-5)//3
hits = []
def prodcounts(R):
  return Counter(x*w for x in R for w in R)
for lo in ("0", "1", "-k"):
  for s in range(-3, 4):
    for al in range(0, 4):
      for be in range(-4, 5):
        for kind in ("det", "perm", "absdet"):
          ok = True
          for n in range(3, 11):
            k = n + s
            if k < 1: ok = False; break
            R = range({"0":0,"1":1,"-k":-k}[lo], k+1)
            P = prodcounts(R); D = al*n + be
            if kind == "det": c = sum(v*P.get(u+D,0) for u,v in P.items())
            elif kind == "perm": c = sum(v*P.get(D-u,0) for u,v in P.items())
            else: c = sum(v*(P.get(u+D,0) + (P.get(u-D,0) if D else 0)) for u,v in P.items())
            if c != a(n-2): ok = False; break
          if ok: hits.append((lo, s, al, be, kind))
print(hits)
