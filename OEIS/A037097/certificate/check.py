# Check the bit-flip lemmas and the divisibility claims for A037096/A037097/A036284 numerically.
def fib(k):
    a,b=0,1
    for _ in range(k): a,b=b,a+b
    return a
def polydiv_pow(a, d, e):
    # is GF(2) polynomial a (int bitmask) divisible by d^e ? return max e' <= e found
    def mod(x,y):
        dy=y.bit_length()
        while x and x.bit_length()>=dy: x^=y<<(x.bit_length()-dy)
        return x
    def div(x,y):
        q=0; dy=y.bit_length()
        while x and x.bit_length()>=dy:
            s=x.bit_length()-dy; q|=1<<s; x^=y<<s
        return q
    c=0
    while a and mod(a,d)==0: a=div(a,d); c+=1
    return c
for n in range(3,12):
    M=2**(n-2)
    q=[(3**k>>n)&1 for k in range(2*M)]
    assert all(q[k+M]==1-q[k] for k in range(M))
    Q=sum(b<<k for k,b in enumerate(q))
    P=sum((((3**k)>>n)&1)<<k for k in range(2**n))
    assert polydiv_pow(Q,3,10**6)==M-1, n
    assert polydiv_pow(P,3,10**6)==3*M-1, n
for n in range(1,10):
    L=3*2**(n-1)
    q=[(fib(k)>>n)&1 for k in range(2*L)]
    if n>=2: assert all(q[k+L]^q[k]==(1 if k%3 else 0) for k in range(L))
    A=sum(b<<k for k,b in enumerate(q))
    e9=polydiv_pow(A,9,10**6)  # x^3+1 = 0b1001
    e3=polydiv_pow(A,3,10**6)
    print(n, "x^3+1 exp", e9, "need", 2**(n-1)-1, " x+1 exp", e3)
print("ok")
