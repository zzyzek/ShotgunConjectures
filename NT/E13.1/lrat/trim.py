# Backward trim of an LRAT proof: keep only additions reachable from the last (empty) clause via
# hints, renumber consecutively after the M input clauses. Usage: trim.py M in.lrat out.lrat
import sys
M=int(sys.argv[1]); adds={}; order=[]
for line in open(sys.argv[2]):
  t=line.split()
  if not t or t[1]=="d": continue
  i=int(t[0]); z=t.index("0",1)
  adds[i]=(t[1:z],[int(h) for h in t[z+1:-1]]); order.append(i)
last=order[-1]; assert adds[last][0]==[]
need={last}; 
for i in reversed(order):
  if i in need:
    for h in adds[i][1]:
      if h>M: need.add(h)
new={}; k=M; out=open(sys.argv[3],"w"); H=0
for i in order:
  if i in need:
    k+=1; new[i]=k; lits,hs=adds[i]
    hh=[new[h] if h>M else h for h in hs]; H+=len(hh)
    out.write("%d %s0 %s 0\n"%(k," ".join(lits)+(" " if lits else ""), " ".join(map(str,hh))))
print("kept",len(need),"of",len(order),"hints",H)
