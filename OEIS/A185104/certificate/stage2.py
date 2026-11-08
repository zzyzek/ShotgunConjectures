# Stage 2: expand surviving count vectors into numbers, test N and every
# single swap.  A composite verdict from sympy.isprime is a proof (failed
# strong-probable-prime/Lucas test); terms found are listed for separate
# primality proof.  Also brute force all n-digit numbers for n <= 6.
import re, itertools, sys
from sympy import isprime
def swaps(s):
  out=set()
  for i in range(len(s)):
    for j in range(i+1,len(s)):
      if s[i]!=s[j]:
        t=list(s); t[i],t[j]=t[j],t[i]; out.add(''.join(t))
  return out
def is_term(s):
  return isprime(int(s)) and all(isprime(int(t)) for t in swaps(s))
brute=[p for p in range(10,10**6) if is_term(str(p))]
print("brute <10^6:",brute)
D="1379"
found=[]
for n in range(5,24):
  cnt=0
  for line in open(f"surv{n}.txt"):
    cl=[list(map(int,x.split(','))) for x in re.findall(r'\[([0-9,]+)\]',line)]
    pos=[[i for i in range(n) if i%6==r] for r in range(6)]
    per=[]
    for r in range(6):
      ms=''.join(D[d]*cl[r][d] for d in range(4))
      per.append(sorted(set(itertools.permutations(ms))))
    for combo in itertools.product(*per):
      dig=['']*n
      for r in range(6):
        for k,i in enumerate(pos[r]): dig[i]=combo[r][k]
      s=''.join(reversed(dig))
      cnt+=1
      if is_term(s): found.append(s)
  print(n,cnt,"terms:",[x for x in found if len(x)==n]); sys.stdout.flush()
