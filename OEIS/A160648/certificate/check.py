# A160648 vs partitions of 2n+2 with parts >= 3 and largest part of multiplicity >= 3
import sys
M=int(sys.argv[1])
p=[1]+[0]*(2*M+10)
for k in range(1,len(p)):
    for i in range(k,len(p)): p[i]+=p[i-k]
a053445=[p[n+2]-2*p[n+1]+p[n] for n in range(2*M+6)]
a160644=[a053445[2*n] for n in range(M+3)]
# A160648 offset 1: data 0,1,0,0,2,... = second differences of A160644 starting A160644(0..2)
a160648={1:0}
a160648.update({n: a160644[n]-2*a160644[n-1]+a160644[n-2] for n in range(2,M+1)})
# c(m): parts>=3, three largest equal; via GF sum_{j>=3} x^{3j} prod_{k=3..j} 1/(1-x^k)
N=2*M+4
c=[0]*(N+1)
for j in range(3,N//3+1):
    s=[0]*(N+1); s[3*j]=1
    for k in range(3,j+1):
        for i in range(k,N+1): s[i]+=s[i-k]
    for i in range(N+1): c[i]+=s[i]
bad=[n for n in range(1,M+1) if a160648[n]!=c[2*n+2]+(1 if n==2 else 0)]
print("first terms",[a160648[n] for n in range(1,12)],"c:",[c[2*n+2] for n in range(1,12)])
print("mismatch n:",bad)
