# D2: x^n + y^n = n! z^n ; check n=3 witness and small search n=3..6
from math import factorial
print(17**3+37**3, 6*21**3, 17**3+37**3 == 6*21**3)
for n in range(3,7):
    f=factorial(n); sols=[]
    pw={}
    B=400
    for z in range(1,B):
        pw[f*z**n]=z
    for x in range(1,B*3):
        for y in range(x,B*3):
            s=x**n+y**n
            if s in pw: sols.append((x,y,pw[s]))
    print(n, sols[:5])
