LIM=10**30
seq=set()
for m in range(1,110):
    for l in range(0,m):
        for k in range(0,l):
            x=2**m-2**l-3*2**k
            if x>0 and x%9==0 and x//9<LIM: seq.add(x//9)
s=sorted(seq)
data=[1,2,3,4,5,6,8,10,12,13,16,20,21,24,26,32,40,42,48,52,53,64,80,84,85,96,104,106,113,128,160,168,170,192,208,212,213,226,227,256,320,336,340,341,384,416,424,426,452,453,454,512,640,672,680]
print("data match:", s[:len(data)]==data)
def odd(x):
    while x%2==0: x//=2
    return x
odds=set(odd(a) for a in s)
def F(K0):
    f=set()
    for M in range(1,40):
        c=(8**M-(-1)**M-3)
        assert c%6==0; c//=6
        for K in range(K0,60):
            v=c*4**K-1
            if v%3==0 and v//3<LIM: f.add(v//3)
    return f
bound=10**15
o=set(x for x in odds if x<bound)
for K0 in (1,0):
    f=set(x for x in F(K0) if x<bound)
    print("K>=%d: odd parts not in formula:"%K0, sorted(o-f)[:10], " formula values not odd parts:", sorted(f-o)[:10])
