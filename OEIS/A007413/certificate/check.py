# A007413 vs counts of 1's between consecutive 2's of A076826, and the
# formula a(n) = 2 + t(n-1) - t(n) (t = Thue-Morse), against both b-files and
# the morphism 1->123, 2->13, 3->2 iterated from 1.
#
import sys
t=lambda n: bin(n).count('1')%2
def rd(f): return [int(l.split()[1]) for l in open(f) if l.strip() and not l.startswith('#')]
a=rd(sys.argv[1]); b=rd(sys.argv[2])
sig={1:[1,2,3],2:[1,3],3:[2]}
w=[1]
while len(w)<200000: w=[x for y in w for x in sig[y]]
assert w[:len(a)]==a
N=150000
bb=[]; s=0
for n in range(4*N):
  s+=t(n); bb.append(2*s-n)
assert bb[:len(b)]==b
two=[i for i,v in enumerate(bb) if v==2]
cnt=[sum(1 for i in range(two[k]+1,two[k+1]) if bb[i]==1) for k in range(len(two)-1)]
m=min(len(cnt),N)
assert cnt[:m]==w[:m]; assert all(w[n-1]==2+t(n-1)-t(n) for n in range(1,m))
print("ok: morphism = b-file (",len(a),"), A076826 = b-file (",len(b),"), claim for n <=",m)
