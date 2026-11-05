# A104895 via its %F rule a(2^k+j) = a(j) + 2^k (a(j)<0) / a(j) - 2^k (a(j)>=0),
# compared with the %N rule as printed, with -A065620, and with the positions claim.
#
N=1<<16
a=[0]*N; nrule=[0]*N; b=[0]*N
for n in range(1,N):
  k=n.bit_length()-1; j=n-(1<<k)
  a[n]=a[j]+(1<<k) if a[j]<0 else a[j]-(1<<k)
  nrule[n]=-2*nrule[n//2] if n%2==0 else 2*nrule[n//2]-1
  b[n]= 2*b[n//2] if n%2==0 else -2*b[n//2]+1
data=[0,-1,-2,1,-4,3,2,-3,-8,7,6,-7,4,-5,-6,5,-16,15,14,-15,12,-13,-14,13]
print("F-rule matches data:",a[:24]==data," N-rule as printed matches data:",nrule[:24]==data)
print("a = -A065620:",all(a[n]==-b[n] for n in range(N)))
print("a(2n)=2a(n), a(2n+1)=-2a(n)-1:",all(a[2*n]==2*a[n] and a[2*n+1]==-2*a[n]-1 for n in range(N//2)))
pos={}
for n in range(N): pos.setdefault(a[n],n)
print("injective:",len(set(a))==N,
      " pos(k)=A048724(k):",all(pos.get(k)==(k^(2*k)) for k in range(0,4000)),
      " pos(-k)=A065621(k):",all(pos.get(-k)==(k^(2*(k-(k&-k)))) for k in range(1,4000)))
