import sys
from collections import Counter, deque
def run(stages):
  # toothpick: (cx,cy,dir) dir 0 vertical,1 horizontal; endpoints at center +-1
  tp=set(); ends=Counter(); mids=set()
  segs=set()  # unit segments: ((x1,y1),(x2,y2)) sorted
  def add(cx,cy,d):
    tp.add((cx,cy,d))
    e=[(cx,cy-1),(cx,cy+1)] if d==0 else [(cx-1,cy),(cx+1,cy)]
    for p in e: ends[p]+=1
    mids.add((cx,cy))
    if d==0: segs.add(((cx,cy-1),(cx,cy))); segs.add(((cx,cy),(cx,cy+1)))
    else: segs.add(((cx-1,cy),(cx,cy))); segs.add(((cx,cy),(cx+1,cy)))
    return e
  # points touched by toothpicks: endpoint touches another toothpick if point lies on another toothpick
  occ=Counter()  # number of toothpicks containing point
  newest=[]
  def pts(cx,cy,d):
    return [(cx,cy-1),(cx,cy),(cx,cy+1)] if d==0 else [(cx-1,cy),(cx,cy),(cx+1,cy)]
  allt=[]
  def place(c):
    add(*c); allt.append(c)
    for p in pts(*c): occ[p]+=1
  place((0,0,0)); last=[(0,0,0)]
  for s in range(2,stages+1):
    cand=Counter()
    for (cx,cy,d) in last:
      for p in ([(cx,cy-1),(cx,cy+1)] if d==0 else [(cx-1,cy),(cx+1,cy)]):
        if occ[p]==1:  # exposed endpoint
          cand[(p[0],p[1],1-d)]+=1
    new=[c for c,k in cand.items() if k==1]
    # a new toothpick's midpoint must touch exactly one endpoint; also no crossing:
    # two candidates that overlap -> standard rule: if two new toothpicks would touch midpoint-to-endpoint... use APS rule: exposed endpoint gets one; collisions where two new share the same center excluded by k==1
    for c in new: place(c)
    last=new
  return allt, segs
if __name__=="__main__":
  K=int(sys.argv[1])
  a=[]
  for n in range(1,40):
    allt,_=run(n); a.append(len(allt))
  print(a)
