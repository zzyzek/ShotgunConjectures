# Minimal forward DRUP/DRAT checker (second-reader tool, not optimised).
# Every added lemma must be RUP w.r.t. the original clauses plus earlier
# lemmas (deletions are ignored, which is sound), or RAT on its first literal.
# Accepts iff the empty clause is derived.
#
import sys
def read_cnf(fn):
  cls = []
  for l in open(fn):
    if l[0] in 'cp': continue
    xs = [int(x) for x in l.split()]
    if xs: cls.append(xs[:-1])
  return cls
class DB:
  def __init__(s):
    s.cls = []; s.watch = {}; s.units = []
  def add(s, c):
    i = len(s.cls); s.cls.append(list(c))
    if len(c) == 1: s.units.append(i)
    for l in c[:2]: s.watch.setdefault(l, []).append(i)
  def propagate(s, assum):
    # returns True on conflict
    val = {}
    trail = []
    def setl(l):
      if val.get(-l): return False
      if l in val: return True
      val[l] = True; trail.append(l); return True
    for l in assum:
      if not setl(l): return True
    for i in s.units:
      if not setl(s.cls[i][0]): return True
    # empty clause in DB
    qi = 0
    while qi < len(trail):
      f = -trail[qi]; qi += 1
      ws = s.watch.get(f, [])
      j = 0
      while j < len(ws):
        i = ws[j]; c = s.cls[i]
        if c[0] == f: c[0], c[1] = c[1], c[0]
        if val.get(c[0]):
          j += 1; continue
        moved = False
        for k in range(2, len(c)):
          if not val.get(-c[k]):
            c[1], c[k] = c[k], c[1]
            s.watch.setdefault(c[1], []).append(i)
            ws[j] = ws[-1]; ws.pop(); moved = True; break
        if moved: continue
        if val.get(-c[0]): return True
        setl(c[0]); j += 1
    return False
cnf = read_cnf(sys.argv[1])
db = DB()
for c in cnf:
  if len(c) == 0: print("empty clause in CNF"); sys.exit()
  db.add(c)
n_rup = n_rat = 0
for line in open(sys.argv[2]):
  xs = line.split()
  if not xs or xs[0] == 'd': continue
  lem = [int(x) for x in xs[:-1]]
  if db.propagate([-l for l in lem]):
    n_rup += 1
  else:
    if not lem: print("FAIL: empty clause not RUP"); sys.exit(1)
    p = lem[0]; ok = True
    for c in list(db.cls):
      if -p in c:
        res = [-l for l in lem] + [-l for l in c if l != -p]
        if not db.propagate(res): ok = False; break
    if not ok: print("FAIL at lemma", lem); sys.exit(1)
    n_rat += 1
  if not lem: print("VERIFIED: empty clause derived; RUP lemmas", n_rup, "RAT lemmas", n_rat); sys.exit(0)
  if len(lem) == 1: db.add(lem)
  else: db.add(lem)
# proof may end without explicit empty clause: check top-level conflict
print("VERIFIED (top-level conflict)" if db.propagate([]) else "FAIL: no empty clause", "RUP", n_rup, "RAT", n_rat)
