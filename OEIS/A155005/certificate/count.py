def divisors(n):
    ds=[]; d=1
    while d*d<=n:
        if n%d==0:
            ds.append(d)
            if d*d!=n: ds.append(n//d)
        d+=1
    return sorted(ds)
def A121041(n): s=str(n); return sum(str(d) in s for d in divisors(n))
for k in range(1,9):
    v=1125*10**k
    print(k, 5+5*k, v, A121041(v), [d for d in divisors(v) if str(d) in str(v)] if k==3 else '')
print(A121041(3124800))
