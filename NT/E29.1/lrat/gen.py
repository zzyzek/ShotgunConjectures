# Write the chunk modules E29Lrat/Cxx.lean (each: theorems `steps S n k = true`, at most
# CH hints per theorem, at most FH hints per module) and the composition E29Lrat/Steps.lean.
# Reads data/e29.lrat (ids must be consecutive from 16379). Usage: gen.py [CH] [FH] [maxmods]
#
import sys
CH = int(sys.argv[1]) if len(sys.argv) > 1 else 8000
FH = int(sys.argv[2]) if len(sys.argv) > 2 else 300000
MAXM = int(sys.argv[3]) if len(sys.argv) > 3 else 10**9
M = 16378
hints = []
for line in open("data/e29.lrat"):
  t = line.split()
  if (not t) or t[1] == "d":
    continue
  assert int(t[0]) == M + 1 + len(hints), "ids not consecutive"
  z = t.index("0", 1)
  hints.append(len(t) - z - 2)
last = M + len(hints)
# Chunks: consecutive runs of steps with at most CH hints.
chunks, n, k, h = [], M + 1, 0, 0
for i, c in enumerate(hints):
  if k > 0 and h + c > CH:
    chunks.append((n, k, h)); n, k, h = n + k, 0, 0
  k += 1; h += c
chunks.append((n, k, h))
# Modules: consecutive chunks with at most FH hints.
mods, cur, ch = [], [], 0
for c in chunks:
  if cur and ch + c[2] > FH:
    mods.append(cur); cur, ch = [], 0
  cur.append(c); ch += c[2]
mods.append(cur)
nall = len(mods)
mods = mods[:MAXM]
names = []
for j, ms in enumerate(mods):
  nm = "C%02d" % j
  names.append(nm)
  L = ["import E29Lrat.Store", "",
       "/-! # NT-E29.1: LRAT steps %d..%d (%d hints), kernel-checked RUP -/" %
       (ms[0][0], ms[-1][0] + ms[-1][1] - 1, sum(c[2] for c in ms)), "",
       "namespace E29Lrat", "", "open OpenProblemsLib.LRAT", ""]
  for (n, k, h) in ms:
    L.append("theorem s%d : steps S %d %d = true := by decide +kernel" % (n, n, k))
  L += ["", "end E29Lrat", ""]
  open("E29Lrat/%s.lean" % nm, "w").write("\n".join(L))
if MAXM >= nall:
  L = ["\n".join("import E29Lrat.%s" % nm for nm in names), "",
       "/-! # NT-E29.1: all LRAT steps 16379..%d, joined from the chunk theorems -/" % last, "",
       "namespace E29Lrat", "", "open OpenProblemsLib.LRAT", ""]
  allc = [c for ms in mods for c in ms]
  L.append("theorem steps_all : steps S %d %d = true := by" % (M + 1, last - M))
  n0, k0 = allc[0][0], allc[0][1]
  L.append("  have h0 : steps S %d %d = true := s%d" % (n0, k0, n0))
  for j, (n, k, h) in enumerate(allc[1:], 1):
    L.append("  have h%d : steps S %d %d = true := steps_join h%d s%d rfl rfl" % (j, M + 1, k0 + k, j - 1, n))
    k0 += k
  assert k0 == last - M
  L.append("  exact h%d" % (len(allc) - 1))
  L += ["", "end E29Lrat", ""]
  open("E29Lrat/Steps.lean", "w").write("\n".join(L))
print("last", last, "hints", sum(hints), "chunks", len(chunks), "modules", len(mods), " ".join(names))
