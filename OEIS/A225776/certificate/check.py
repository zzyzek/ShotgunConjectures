# A225776 general r: f(r,k) = sum_j C(k,j)^r.
# (1) f(r,k) equals the average of L^k over the N-th-root grid, N > k,
#     L = 2^r cos(sum t_i/2) prod cos(t_i/2) (real), r-1 angles: moment sequence.
# (2) Hankel det H(r,n) = |f(r,i+j)|_{0..n}: positive, H/2^n odd integer.
from math import comb, cos, pi, prod
from itertools import product
from sympy import Matrix
def f(r,k): return sum(comb(k,j)**r for j in range(k+1))
for r in (2,3,4):
  N=9
  pts=[2**r*cos(sum(t)/2)*prod(cos(x/2) for x in t) for t in product([2*pi*a/N for a in range(N)],repeat=r-1)]
  for k in range(N):
    m=sum(p**k for p in pts)/len(pts)
    assert abs(m-f(r,k))<1e-6*max(1,f(r,k)),(r,k,m,f(r,k))
print("moment representation ok r=2..4, k<9")
for r in range(2,8):
  for n in range(0,9):
    H=Matrix(n+1,n+1,lambda i,j:f(r,i+j)).det()
    assert H>0 and H%(2**n)==0 and (H//2**n)%2==1,(r,n,H)
print("H(r,n) > 0, H/2^n odd: r=2..7, n=0..8")
