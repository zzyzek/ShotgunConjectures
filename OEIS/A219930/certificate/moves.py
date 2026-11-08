# certificate: exceptional primes and exponent bounds for members n of A219930 with q not dividing n
from sympy import primerange, isprime
def has_s(lo,hi,q):
    # prime s != q with lo < s < hi (strict, rational bounds given as fractions)
    from fractions import Fraction
    import math
    a=math.floor(lo)+1; b=math.ceil(hi)-1
    return [s for s in range(max(a,2),b+1) if isprime(s) and s!=q][:1]
from fractions import Fraction as F
for q in (3,5):
    E=[p for p in primerange(2,10**4) if p!=q and not has_s(F(p,q),F(p-1,q-1),q)]
    print("q",q,"exceptional primes (<1e4):",E)
    bound=1; 
    for p in E:
        j=1
        while not has_s(F(p**j,q),F(p**j,q-1),q): j+=1
        print("  p",p,"exponent <=",j); bound*=p**j
    print("  n <=",bound)
