N=20000
phi=list(range(N+1))
for i in range(2,N+1):
  if phi[i]==i:
    for j in range(i,N+1,i): phi[j]-=phi[j]//i
L=N//2
# A066362(n) for n<=L (least k>n with phi(k)<phi(n)); 0 if none up to N (phi(k)>=sqrt(k/2) so ok for small)
vals=set(); zeros=[]
for n in range(1,L+1):
  k=next((k for k in range(n+1,N+1) if phi[k]<phi[n]),0)
  if k: vals.add(k)
  else: zeros.append(n)
A=[n for n in range(1,L+1) if all(phi[m]>=phi[n] for m in range(n+1,N+1))]
print(A[:20]); print(A==zeros)
S=set(A)-{1,2,3,4}
vb=sorted(v for v in vals if v<=L//2)
print("values not in A122957:",[v for v in vb if v not in S][:15])
print("A122957 not values:",[v for v in sorted(S) if v<=L//2 and v not in vals][:15])
