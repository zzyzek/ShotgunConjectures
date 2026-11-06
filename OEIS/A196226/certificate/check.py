# A196226: list terms m <= N (sigma(m) mod m = 3 + m/2) and test Layman's three congruences.
import sys
N=int(sys.argv[1]) if len(sys.argv)>1 else 200000
sig=[[0]*(N+1) for _ in range(5)]
for d in range(1,N+1):
  for m in range(d,N+1,d):
    for k in range(1,5): sig[k][m]+=d**k
for m in range(2,N+1,2):
  if sig[1][m]%m==3+m//2:
    bad=[k for k,c,t in ((2,5,14),(3,9,22),(4,17,38)) if m>=t and sig[k][m]%m!=(c+m//2)%m]
    if bad: print("term",m,"violates k =",bad)
