# Recurrence from OEIS A224529 (Somos); check Theorem 1.2 (r=1) of Osburn-Sahu.
from fractions import Fraction
N=1000
a=[1,2,6,26,142,876]
for n in range(6,N+1):
  s=(14*n*n-21*n+9)*a[n-1]+(-57*n*n+171*n-136)*a[n-2]+(106*n*n-477*n+551)*a[n-3]+(-90*n*n+540*n-816)*a[n-4]+(16*n*n-120*n+224)*a[n-5]+(19*n*n-171*n+380)*a[n-6]
  assert s%(n*n)==0; a.append(s//(n*n))
b=[int(l.split()[1]) for l in open('oeis/b224529.txt') if l.strip() and not l.startswith('#')]
assert a[:len(b)]==b, 'bfile mismatch'
ps=[p for p in range(2,500) if all(p%q for q in range(2,p)) and pow(p,11,23)==1]
cnt=0
for p in ps:
  for n in range(1,N//p+1):
    assert (a[n*p]-a[n])%p==0,(p,n); cnt+=1
print('checked',cnt,'pairs, primes',ps[:12])
