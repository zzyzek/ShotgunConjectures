# Count primitive cyclic words among candidate files (words with first face 0, all rotations present
# only for those starting with 0).  Primitive = not a proper power.
import sys
for path in sys.argv[1:]:
  ws = [l.strip() for l in open(path) if l.strip()]
  k = len(ws[0]) if ws else 0
  prim = [s for s in ws if not any(k % d == 0 and s == s[:d]*(k//d) for d in range(1, k))]
  cyc = set(min(s[i:]+s[:i] for i in range(k)) for s in prim)
  print(path, 'candidates', len(ws), 'primitive', len(prim), 'cyclic classes (min rotation)', len(cyc))
