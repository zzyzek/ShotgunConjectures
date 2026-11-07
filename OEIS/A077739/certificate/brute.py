# brute force: smallest multiple of n beginning and ending with str(n), digit sum n
import sys
def ok(N,n):
    s=str(N); t=str(n)
    return s.startswith(t) and s.endswith(t) and sum(map(int,s))==n
def a(n, lim=10**8):
    k=1
    while k*n<lim*n and k<lim:
        if ok(k*n,n): return k*n
        k+=1
    return None
for n in range(1,41):
    if n in (11,17,19): print(n,'skip'); continue
    print(n, a(n, 10**7))
