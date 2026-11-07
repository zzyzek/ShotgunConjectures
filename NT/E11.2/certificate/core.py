# Backward-trim an LRAT proof (as E13.1/lrat/trim.py) and also report the
# original clauses used (the unsat core).  usage: core.py M in.lrat core_ids.txt
import sys
M=int(sys.argv[1]); adds={}; order=[]
for line in open(sys.argv[2]):
  t=line.split()
  if not t or t[1]=="d": continue
  i=int(t[0]); z=t.index("0",1)
  adds[i]=[int(h) for h in t[z+1:-1]]; order.append(i)
need={order[-1]}; core=set()
for i in reversed(order):
  if i in need:
    for h in adds[i]:
      if h>M: need.add(h)
      else: core.add(h)
open(sys.argv[3],"w").write("\n".join(map(str,sorted(core))))
print("additions kept",len(need),"of",len(order),"core",len(core),"of",M)
