# Explicit form for d = n-4 (n odd): f = sum over 4-sets S of (max S - min S) * sign(S, S^c) * e_{S^c}.
# Full Hilbert series mod P compared with the LN bound.
import sys, itertools
exec(open('hs.py').read())
def perm_sign(seq):
    s=1
    for a in range(len(seq)):
        for b in range(a+1,len(seq)):
            if seq[a]>seq[b]: s=-s
    return s
for n in [int(a) for a in sys.argv[1:]]:
    d=n-4; f=[]
    for S in itertools.combinations(range(n),4):
        Sc=[i for i in range(n) if i not in S]
        c=(S[3]-S[0])*perm_sign(list(S)+Sc)
        f.append((sum(1<<i for i in Sc), c%P))
    h=HS(n,f,d); a=LN(n,d)
    print(n,d,h,a,'OK' if h==a else 'no',flush=True)
