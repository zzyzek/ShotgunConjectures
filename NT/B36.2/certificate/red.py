# check: phi(m) = 2 mod 4 iff m in {4, p^a, 2p^a : p = 3 mod 4}; and reduced search for phi(n+3)=phi(n)+2 to N
import sys
from sympy import totient, factorint
N=int(sys.argv[1])
ph=list(range(N+4))
for i in range(2,N+4):
    if ph[i]==i:
        for j in range(i,N+4,i): ph[j]-=ph[j]//i
def special(m):
    if m==4: return True
    f=factorint(m); f.pop(2,None) if m%4!=0 and m%2==0 else None
    return len(f)==1 and list(f)[0]%4==3 and (m%4!=0)
bad=[m for m in range(3,200000) if (ph[m]%4==2)!=special(m)]
print("char mismatches",bad[:5])
sols=[n for n in range(1,N+1) if ph[n+3]==ph[n]+2]
print("solutions <=",N,sols)
