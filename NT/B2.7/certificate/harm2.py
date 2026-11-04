from sympy import factorint, divisor_sigma as S, divisor_count as D
from math import gcd
def H(n): return n*D(n)/S(n)
for n in [29495815011600,1179832600464,9831938337200,12757657068800,25075635936512]:
    print(n, factorint(n), "H=",H(n), "sigma%d=",S(n)%D(n))
a,b,n=1179832600464,9831938337200,29495815011600
print("unitary:",n%a==0 and gcd(a,n//a)==1, n%b==0 and gcd(b,n//b)==1)
