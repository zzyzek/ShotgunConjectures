import itertools
def a(n): return n*(2*n*n+6*n-5)//3
target = {n: a(n-2) for n in range(3, 11)}
ranges = {"1..n":lambda n:range(1,n+1), "0..n":lambda n:range(0,n+1), "-n..n":lambda n:range(-n,n+1),
  "0..n-1":lambda n:range(0,n), "1..n-1":lambda n:range(1,n), "-n..0":lambda n:range(-n,1), "1..2n":lambda n:range(1,2*n+1), "0..2n":lambda n:range(0,2*n+1)}
funcs = {"det":lambda x,y,z,w:x*w-y*z, "perm":lambda x,y,z,w:x*w+y*z, "absdet":lambda x,y,z,w:abs(x*w-y*z),
  "sum":lambda x,y,z,w:x+y+z+w, "trace":lambda x,y,z,w:x+w}
Ds = {"n":lambda n:n,"2n":lambda n:2*n,"n-1":lambda n:n-1,"n+1":lambda n:n+1,"2n-1":lambda n:2*n-1,"2n+1":lambda n:2*n+1,"0":lambda n:0,"1":lambda n:1,"2":lambda n:2,"n-2":lambda n:n-2,"2n-2":lambda n:2*n-2}
rels = {"=":lambda v,D:v==D, ">=":lambda v,D:v>=D, "<=":lambda v,D:v<=D, ">":lambda v,D:v>D, "<":lambda v,D:v<D}
hits = []
for rn, R in ranges.items():
  for fn, f in funcs.items():
    vals = {}
    for n in range(3, 9):
      vals[n] = [f(*m) for m in itertools.product(R(n), repeat=4)]
    for dn, D in Ds.items():
      for reln, rel in rels.items():
        ok = all(sum(1 for v in vals[n] if rel(v, D(n))) == target[n] for n in range(3, 9))
        if ok: hits.append((rn, fn, reln, dn))
print(hits)
