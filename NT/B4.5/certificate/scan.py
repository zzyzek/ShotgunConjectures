from sympy import factorint
from math import gcd
A=[int(l.split()[1]) for l in open('b002952.txt') if l.strip() and not l.startswith('#')]
B=[int(l.split()[1]) for l in open('b002953.txt') if l.strip() and not l.startswith('#')]
assert len(A)==len(B)
def ss(n):
    r=1
    for p,e in factorint(n).items(): r*=1+p**e
    return r
odd=[];cop=[];bad=0
for m,n in zip(A,B):
    if m%2==1 or n%2==1:
        fm,fn=factorint(m),factorint(n)
        odd.append((m,n,fm,fn, all(e==1 for e in fm.values()) and all(e==1 for e in fn.values()), ss(m)==m+n==ss(n)))
    if gcd(m,n)==1: cop.append((m,n))
print("pairs",len(A),"max smaller",max(A))
print("odd pairs",len(odd))
for o in odd: print(o)
print("coprime",cop)
