# Test the cyclic d = 3 form f = sum_i x_i x_{i+1} x_{i+3} (indices mod n) against the LN bound.
import sys
exec(open('seeds.py').read().split("n=int(sys.argv[1])")[0])
seed=tuple(int(s) for s in sys.argv[3].split(','))
for n in range(int(sys.argv[1]),int(sys.argv[2])+1):
    d=len(seed)
    if n==9 and d==3: continue
    a=LN(n,d); f=list(orbit(seed,n).items())
    print(n,d,seed,'OK' if ok(n,d,f,a) else 'no',flush=True)
