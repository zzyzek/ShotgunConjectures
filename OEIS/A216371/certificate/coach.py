from sympy import primerange, n_order
def odd(n):
    while n%2==0: n//=2
    return n
def top(b):
    a=1; row=[]
    while True:
        row.append(a); a=odd(b-a)
        if a==1: return row
def sord(b):
    m=1
    while pow(2,m,b) not in (1,b-1): m+=1
    return m
cnt=0
for p in primerange(3,20000):
    one = (p-1)//(2*sord(p))==1
    q=(p+1)//4
    perm = sorted(top(p))==list(range(1,2*q,2))
    assert one==perm,(p,one,perm)
    cnt+=one
print("ok",cnt, top(11),top(13),top(37))
