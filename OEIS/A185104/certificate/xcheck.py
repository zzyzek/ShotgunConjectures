# Soundness cross-check of the count-vector sieve: for n = 5..10, every n-digit
# number over {1,3,7,9} is either an arrangement of a surviving count vector,
# or it or one of its swaps is divisible by 3, 7, 11, 13 or 37.
import itertools,re
D="1379"
for n in range(5,11):
  surv=set()
  for line in open(f"surv{n}.txt"):
    cl=tuple(tuple(map(int,x.split(','))) for x in re.findall(r'\[([0-9,]+)\]',line))
    surv.add(cl)
  bad=0
  for t in itertools.product(D,repeat=n):
    s=''.join(t)
    cl=tuple(tuple(sum(1 for i in range(n) if i%6==r and s[n-1-i]==d) for d in D) for r in range(6))
    if cl in surv: continue
    N=int(s)
    killed = any(N%p==0 for p in (3,7,11,13,37))
    if not killed:
      for i in range(n):
        for j in range(i+1,n):
          if s[i]!=s[j]:
            u=list(s);u[i],u[j]=u[j],u[i];M=int(''.join(u))
            if any(M%p==0 for p in (7,11,13,37)): killed=True;break
        if killed: break
    if not killed: bad+=1
  print(n,"unsound:",bad)
