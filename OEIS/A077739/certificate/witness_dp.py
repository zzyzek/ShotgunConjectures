# find a witness N = n*10^(L+D) + mid*10^D + n, mid has L digits (leading zeros ok), ds(mid)=n-2s(n), n|N
def ds(x): return sum(map(int,str(x)))
def wit(n):
    D=len(str(n)); r=n-2*ds(n)
    if r<0: return None
    for L in range(0,40):
        # target: mid*10^D ≡ -(n*10^(L+D)+n) mod n  -> mid*10^D ≡ 0 mod n
        # DP over mid digits from most significant; state (val mod n, sum)
        states={(0,0):None}
        layers=[states]
        for pos in range(L):
            nxt={}
            for (v,s) in layers[-1]:
                for d in range(10):
                    if s+d>r: break
                    k=((v*10+d)%n, s+d)
                    if k not in nxt: nxt[k]=((v,s),d)
            layers.append(nxt)
        for (v,s) in layers[-1]:
            if s==r and (v*10**D)%n==0:
                # reconstruct
                digs=[]; st=(v,s)
                for i in range(L,0,-1):
                    prev,d=layers[i][st]; digs.append(d); st=prev
                mid=int(''.join(map(str,reversed(digs))) or '0')
                N=n*10**(L+D)+mid*10**D+n
                assert N%n==0 and ds(N)==n and str(N).startswith(str(n)) and str(N).endswith(str(n))
                return N
    return None
import sys
out={}
for line in open('a77739w.out'):
    n,v=line.split(); n=int(n)
    out[n]=int(v) if v!='None' else wit(n)
for n in sorted(out): print(n,out[n])
