from sympy import isprime
import sys
def a(n):
    m=2*n-1; d=len(str(m))
    return sum(1 for k in range(1,m) if isprime(k*10**d+m))
data=[0,2,0,4,5,4,5,0,4,7,7,9,0,8,9,12,10,0,12,14,11,12,0,16,15,19,17,0,23]
assert [a(n) for n in range(1,len(data)+1)]==data
N=int(sys.argv[1]); bad=[]
for n in range(1,N+1):
    m=2*n-1; d=len(str(m))
    if n%5==3: continue
    z = not any(isprime(k*10**d+m) for k in range(1,m))
    if z != (n%5==3): bad.append(n)
print("mismatches:",bad)
