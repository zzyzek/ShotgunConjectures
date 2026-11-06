# Generate the greedy sequence under three readings: python3 readings.py N self start
# (self = 1 also forbids 2*a(n) in A001333; start = first term, 2 per the data, 1 per the name).
# Prints the terms, the first differences and a(x(k)) at the Pell points x(k).
import sys
N=int(sys.argv[1]); self_ok=int(sys.argv[2]) if len(sys.argv)>2 else 1
P=[1,1]
while P[-1]<10*N: P.append(2*P[-1]+P[-2])
P=sorted(set(P))
S=set(); seq=[]
start=int(sys.argv[3]) if len(sys.argv)>3 else 2
c=start
while c<=N:
  ok=all((p-c) not in S for p in P if p>c)
  if ok and self_ok and (2*c in P): ok=False
  if ok: S.add(c); seq.append(c)
  c+=1
d=[seq[i+1]-seq[i] for i in range(len(seq)-1)]
print(len(seq)); print(seq[:40]); print(d[:110])
x=[1,2]
while x[-1]<len(d): x.append(2*x[-1]+x[-2])
print([(k+1,xk,d[xk-1]) for k,xk in enumerate(x) if xk<=len(d)])
