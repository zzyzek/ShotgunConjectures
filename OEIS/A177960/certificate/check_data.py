# Numeric check: A177960 data vs rows of m-nomial triangles mod 2 (m <= 40, n <= 200).
def row(m,n):
    c=[1]
    for _ in range(n):
        d=[0]*(len(c)+m-1)
        for i,v in enumerate(c):
            if v:
                for j in range(m): d[i+j]^=1
        c=d
    return sum(b<<i for i,b in enumerate(c))
A001317=[row(2,t) for t in range(80)]
other=set(row(m,n) for m in range(3,41) for n in range(0,80))
seq=[x for x in A001317 if x not in other]
data=[3,5,17,51,257,1285,3855,13107,65537,196611,983055,1114129,5570645,16711935,50529027,84215045,858993459,4294967297,21474836485,219043332147,365072220245,1103806595329,3311419785987]
print(seq[:len(data)]==data)
