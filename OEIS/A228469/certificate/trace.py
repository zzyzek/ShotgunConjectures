import sys
def trace(x,y):
    t=[]
    while x%y!=0:
        r=x%y
        if r<=y-r: x,y=y,r; t.append('0')
        else: x,y=y,y-r; t.append('1')
    return ''.join(t)
assert trace(18,13)=='010' and trace(30,19)=='101'
C=int(sys.argv[1]); L=int(sys.argv[2])
best={}
for c in range(1,C):
    for b in range(1,c):
        t=trace(b,c)
        for start in '01':
            alt=(start+('1' if start=='0' else '0'))*40
            if alt.startswith(t) and (start,len(t)) not in best:
                best[(start,len(t))]=(c,b)
for s in '01':
    print(s,[best.get((s,l)) for l in range(1,L)])
