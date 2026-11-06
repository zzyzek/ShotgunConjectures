import sys
N=int(sys.argv[1])
used=bytearray(3*N+10)
a=[0,1]; used[1]=1
k=1  # pointer: smallest integer >= n missing
first={}
for n in range(2,N+1):
    m=max(k,n)
    while used[m]: m+=1
    k=m
    v=n+m; a.append(v); used[v]=1
    d=v-2*n
    if d not in first: first[d]=n
print(sorted(first.items())[:30])
print([ (kk, first.get(kk), 2**kk+2**(kk-1)-kk) for kk in range(2,25) if kk in first])
# print first 120 of a(n)-2n
print([a[n]-2*n for n in range(1,121)])
