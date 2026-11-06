import sympy as sp
n=7
TE=[(0,1),(1,2),(2,3),(3,4),(4,5),(4,6)]
A=sp.zeros(n,n)
for i,d in enumerate([-1,-1,-1,0,-1,0,0]): A[i,i]=d
for a,b in TE: A[a,b]=A[b,a]=1
rref,piv=A.rref(); print(piv)
U=A.extract(list(range(n)),list(piv)); W=rref.extract(list(range(len(piv))),list(range(n)))
assert U*W==A
print(U.tolist()); print(W.tolist())
