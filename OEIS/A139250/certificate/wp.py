# Wall process: generalized toothpick CA.
# wall(p) -> True if lattice point p is blocked.
# pieces: list of (segments, points) of initial pieces; cover counts points.
# active: list of (endpoint, orientation_of_parent) : exposed-candidate endpoints with parent orientation (0 vertical,1 horizontal)
from collections import Counter
def pts(c,d):
  x,y=c
  return [(x,y-1),(x,y),(x,y+1)] if d==0 else [(x-1,y),(x,y),(x+1,y)]
def ends(c,d):
  x,y=c
  return [(x,y-1),(x,y+1)] if d==0 else [(x-1,y),(x+1,y)]
def segs_of(c,d):
  x,y=c
  return [((x,y-1),(x,y)),((x,y),(x,y+1))] if d==0 else [((x-1,y),(x,y)),((x,y),(x+1,y))]
def run(wall, init_segs, init_cover, active, nsteps, start_stage):
  """init_segs: dict seg->stage; init_cover: Counter of covered points;
     active: list of (point, parent_dir, parent_id) endpoints of last stage pieces.
     returns segs dict seg->stage, toothpicks list (center,dir,stage)"""
  segs=dict(init_segs); occ=Counter(init_cover); tps=[]
  last=active  # list of (p, d_parent)
  s=start_stage
  for _ in range(nsteps):
    s+=1
    new=[]
    for (p,dpar) in last:
      if occ[p]==1 and not wall(p): new.append((p,1-dpar))
    nxt=[]
    for (c,d) in new:
      tps.append((c,d,s))
      for q in pts(c,d): occ[q]+=1
      for g in segs_of(c,d): segs[g]=s
    for (c,d) in new:
      for e in ends(c,d): nxt.append((e,d))
    last=nxt
  return segs,tps,occ,last
