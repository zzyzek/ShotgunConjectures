import sys
def zf(c):
    while c:
        if c%3==2: return False
        c//=3
    return True
def exists(k):
    seen=set(); fr=[(0,False)]
    while fr:
        nf=[]
        for c,u in fr:
            for d in (0,1):
                v=k*d+c; r=v%3
                if r==2: continue
                nc=v//3; nu=u or d==1
                if nu and zf(nc): return True
                s=(nc,nu)
                if s not in seen: seen.add(s); nf.append(s)
        fr=nf
    return False
def interval_bad(k):
    # k in (1.5*3^m, 2*3^m) for some m  <=> 3*3^m < 2k < 4*3^m
    p=1
    while p<=k:
        if 3*p<2*k<4*p: return True
        p*=3
    return False
N=int(sys.argv[1]); mism=[]
for k in range(1,N):
    if k%3==0: continue
    pred = (k%3==1) and not interval_bad(k)
    if pred != exists(k): mism.append(k)
print("mismatches:",len(mism),mism[:50])
