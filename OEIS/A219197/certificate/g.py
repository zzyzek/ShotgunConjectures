# For even n with n & 2n = 0 (the n where C(3n+1,n), hence a(n), is odd):
# (i) C(3n+1,n) = (-1)^N mod 4 with N = popcount(n) + #{i>=0 : bit_{i+1}(n) = 1 and bit_i(2n+1) = 1};
# (ii) E(n) = #{0<=k<n : k & (2n+1) = 0, v2(n-k) even} has the parity of N (equivalent to a(n) = 1 mod 4).
from math import comb
def v2(m):
  c=0
  while m%2==0: m//=2; c+=1
  return c
bad1=bad2=cnt=0
for n in range(0, 1<<13, 2):
  if n & (2*n): continue
  cnt+=1
  c=2*n+1
  N=bin(n).count('1')+sum(1 for i in range(0,20) if (n>>(i+1))&1 and (c>>i)&1)
  if comb(3*n+1,n)%4 != (1 if N%2==0 else 3): bad1+=1
  E=sum(1 for k in range(0,n) if k&c==0 and v2(n-k)%2==0)
  if E%2 != N%2: bad2+=1
print("n checked:",cnt,"(i) failures:",bad1,"(ii) failures:",bad2)
