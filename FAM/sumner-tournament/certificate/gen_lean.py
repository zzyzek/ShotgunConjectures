#!/usr/bin/env python3
# Emit the data section of Sumner_mathlib.lean for trees on n <= N vertices:
# tournament class representatives on k <= 2N-2 vertices with extension
# tables, oriented-tree representatives, code -> tree-rep certificates and
# tree-rep -> tournament-rep embeddings.  Usage: gen_lean.py N > data.lean
#
import sys
from gen import build, codes, tree_canon, tree_reps, find_emb, tadj

PER = 64

def packed(vals, w, PER=PER):
  # Chunks of PER fields of width w, little-endian.
  #
  out = []
  for c in range(0, len(vals), PER):
    x = 0
    for t, v in enumerate(vals[c:c+PER]):
      assert v < (1 << w)
      x |= v << (w*t)
    out.append(x)
  return out

def lean_list(xs):
  return "[" + ",\n  ".join(hex(x) for x in xs) + "]"

def par_lists(n):
  # Same order and index as allPar in Lean.
  #
  res = [([], 0)]
  for l in range(n):
    r = max(l, 1)
    res = [(ps + [x], idx*r + x) for ps, idx in res for x in range(r)]
  return res

N = int(sys.argv[1])
M = 2*N - 2
reps, tables = build(M)
out = []
emit = out.append

emit("def numReps : Nat → Nat")
for k in range(1, M+1): emit(f"  | {k} => {len(reps[k])}")
emit("  | _ => 0\n")
emit("def repData : Nat → List Nat")
for k in range(1, M+1):
  emit(f"  | {k} => {lean_list(packed(reps[k], k*(k-1)//2))}")
emit("  | _ => []\n")
emit("def tabData : Nat → List Nat")
for k in range(1, M):
  w = 13 + 3*(k+1)
  rows = []
  for i, row in enumerate(tables[k]):
    x = 0
    for S, (j, seq) in enumerate(row):
      e = j
      for a, v in enumerate(seq): e |= v << (13 + 3*a)
      x |= e << (w*S)
    rows.append(x)
  emit(f"  | {k} => {lean_list(rows)}")
emit("  | _ => []\n")

trs = {n: tree_reps(n) for n in range(2, N+1)}
emit("def numTrees : Nat → Nat")
for n in range(2, N+1): emit(f"  | {n} => {len(trs[n])}")
emit("  | _ => 0\n")
emit("def treeData : Nat → List (List (Nat × Nat))")
for n in range(2, N+1):
  emit(f"  | {n} => [" + ", ".join("[" + ", ".join(f"({a}, {b})" for a, b in arcs) + "]" for arcs in trs[n]) + "]")
emit("  | _ => []\n")

# code certificates: index -> (r, rho)
#
emit("def codeData : Nat → List Nat")
for n in range(2, N+1):
  idx = {tuple(map(tuple, a)): r for r, a in enumerate(trs[n])}
  certs = {}
  for ps, pidx in par_lists(n):
    for d in range(1 << (n-1)):
      arcs = []
      for i in range(1, n):
        x = ps[i]
        arcs.append((x, i) if (d >> (i-1)) & 1 else (i, x))
      key, perm = tree_canon(arcs, n)
      r = idx[key]
      e = r
      for a in range(n): e |= perm[a] << (5 + 3*a)
      certs[pidx * (1 << (n-1)) + d] = e
  vals = [certs[c] for c in range(len(certs))]
  emit(f"  | {n} => {lean_list(packed(vals, 5 + 3*n))}")
emit("  | _ => []\n")

# final embeddings: (i, r) -> f, index i * numTrees + r
#
emit("def embData : Nat → List Nat")
for n in range(2, N+1):
  m = 2*n - 2
  vals = []
  for t in reps[m]:
    for arcs in trs[n]:
      f = find_emb(arcs, n, lambda a, b: tadj(t, a, b), m)
      e = 0
      for a in range(n): e |= f[a] << (3*a)
      vals.append(e)
  emit(f"  | {n} => {lean_list(packed(vals, 3*n, 1024))}")
emit("  | _ => []\n")
print("\n".join(out))
