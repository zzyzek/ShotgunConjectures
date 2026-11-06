# a(n) from the definition (union of the rectangles [1,d] x [1,n/d]) against the OEIS data
# and the bound sum_{k<=n} floor(n/k); prints the n <= 2000 where equality holds (first few).
data=[1,3,5,8,9,14,13,20,21,26,21,35,25,38,41,48,33,57,37,64,61,62,45,84]
def a(n):
    ds=[d for d in range(1,n+1) if n%d==0]
    # column x has height max{n/d : d >= x, d | n}
    return sum(max(n//d for d in ds if d>=x) for x in range(1,n+1))
assert [a(n) for n in range(1,25)]==data
eq=[]
for n in range(1,2001):
    s=sum(n//k for k in range(1,n+1)); A=a(n); assert A<=s
    if A==s: eq.append(n)
print("bound holds for n<=2000; equality at",eq[:20],"... count",len(eq))
