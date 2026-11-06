# exp(sum (q-1)((q^n-1)/(q-1))^(n-1) x^n/n): integer coefficients for q = 2..8, n <= 40,
# Gauss congruences b(m p^a) = b(m p^(a-1)) mod p^a, and the A181316 data (q = 3).
from fractions import Fraction
data=[1,2,6,122,32242,85808250,2130201408474,487143290951349930,1021074261736069185881850,19547957495950654924427730234138,3408841202663503254998708590894515413082]
def b(q,n): return (q-1)*((q**n-1)//(q-1))**(n-1)
def series(q,N):
    A=[Fraction(1)]
    for n in range(N):
        A.append(sum(b(q,j+1)*A[n-j] for j in range(n+1))/(n+1))
    return A
for q in range(2,9):
    A=series(q,40)
    assert all(x.denominator==1 for x in A), q
    for p in (2,3,5,7):
        for m in range(1,8):
            for a in range(1,4):
                assert (b(q,m*p**a)-b(q,m*p**(a-1)))%p**a==0
assert [int(x) for x in series(3,10)]==data
print("ok")
