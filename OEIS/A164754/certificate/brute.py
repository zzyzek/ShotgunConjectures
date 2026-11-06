import sys, itertools
def ok(g,n):
    # g: list of rows (a,b)
    cell=lambda i,j:g[i][j]
    for i in range(n):
        for j in range(2):
            c=cell(i,j); s=0
            for (a,b) in ((i-1,j),(i+1,j),(i,1-j)):
                if 0<=a<n and cell(a,b)==c: s+=1
            if s>2: return False
    for c in range(1,5):
        cells=[(i,j) for i in range(n) for j in range(2) if g[i][j]==c]
        seen={cells[0]}; st=[cells[0]]
        while st:
            i,j=st.pop()
            for (a,b) in ((i-1,j),(i+1,j),(i,1-j)):
                if 0<=a<n and (a,b) not in seen and g[a][b]==c:
                    seen.add((a,b)); st.append((a,b))
        if len(seen)!=len(cells): return False
    return True
def sols(n):
    rows=list(itertools.product(range(1,5),repeat=2))
    out=[]
    if n==1: return []
    for mid in itertools.product(rows,repeat=n-2):
        g=[(1,2)]+list(mid)+[(3,4)]
        if ok(g,n): out.append(g)
    return out
if __name__=="__main__":
    for n in range(2,int(sys.argv[1])+1):
        print(n,len(sols(n)),flush=True)
