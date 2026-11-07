from sympy import isprime
def S(e): return e*(e+1)*(2*e+1)//6
def nxt(s):
    L=1
    while True:
        L+=1
        tot=S(s+L-1)-S(s-1)
        if tot%L==0 and isprime(tot//L): return L
a,b=0,1; ia=ib=0
seenA={0:0}; seenB={1:0}
import sys
N=int(sys.argv[1])
while ia<N or ib<N:
    if a<=b:
        a+=nxt(a); ia+=1; seenA[a]=ia
        if a in seenB: print("merge",a,"A idx",ia,"B idx",seenB[a]); break
    else:
        b+=nxt(b); ib+=1; seenB[b]=ib
        if b in seenA: print("merge",b,"A idx",seenA[b],"B idx",ib); break
else: print("no merge",ia,ib,a,b)
