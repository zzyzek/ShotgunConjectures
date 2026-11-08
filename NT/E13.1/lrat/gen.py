# Write the chunk modules E13Lrat/<P>xx.lean (each: theorems `steps S<t> n k = true`, at most
# CH hints per theorem, at most FH hints per module) and the composition E13Lrat/Steps<t>.lean,
# for the store `S<t>` read from data/e13m<t>.cnf and data/e13m<t>.lrat (ids consecutive).
# Usage: gen.py t P [CH] [FH]     (t = 2: P = A; t = 4p: P = P; t = 4n: P = N; t = 4: P = U)
#
import sys
m, P = sys.argv[1], sys.argv[2]
DESC = {"2": "m = 2", "4p": "m = 4, 12 has colour 2", "4n": "m = 4, 12 has not colour 2",
        "4": "m = 4, unsplit"}[m]
CH = int(sys.argv[3]) if len(sys.argv) > 3 else 8000
FH = int(sys.argv[4]) if len(sys.argv) > 4 else 400000
S = "S%s" % m
M = int(open("data/e13m%s.cnf" % m).readline().split()[3])
hints = []
for line in open("data/e13m%s.lrat" % m):
  t = line.split()
  if (not t) or t[1] == "d":
    continue
  assert int(t[0]) == M + 1 + len(hints), "ids not consecutive"
  z = t.index("0", 1)
  hints.append(len(t) - z - 2)
last = M + len(hints)
chunks, n, k, h = [], M + 1, 0, 0
for c in hints:
  if k > 0 and h + c > CH:
    chunks.append((n, k, h)); n, k, h = n + k, 0, 0
  k += 1; h += c
chunks.append((n, k, h))
mods, cur, ch = [], [], 0
for c in chunks:
  if cur and ch + c[2] > FH:
    mods.append(cur); cur, ch = [], 0
  cur.append(c); ch += c[2]
mods.append(cur)
names = []
for j, ms in enumerate(mods):
  nm = "%s%02d" % (P, j)
  names.append(nm)
  L = ["import E13Lrat.Store%s" % m, "",
       "/-! # NT-E13.1, %s: LRAT steps %d..%d (%d hints), kernel-checked RUP -/" %
       (DESC, ms[0][0], ms[-1][0] + ms[-1][1] - 1, sum(c[2] for c in ms)), "",
       "namespace E13Lrat", "", "open OpenProblemsLib.LRAT", ""]
  for (n, k, h) in ms:
    L.append("theorem %s_%d : steps %s %d %d = true := by decide +kernel" % (P, n, S, n, k))
  L += ["", "end E13Lrat", ""]
  open("E13Lrat/%s.lean" % nm, "w").write("\n".join(L))
L = ["\n".join("import E13Lrat.%s" % nm for nm in names), "",
     "/-! # NT-E13.1, %s: all LRAT steps %d..%d, joined from the chunk theorems -/" % (DESC, M + 1, last), "",
     "namespace E13Lrat", "", "open OpenProblemsLib.LRAT", ""]
allc = [c for ms in mods for c in ms]
L.append("theorem steps%s : steps %s %d %d = true := by" % (m, S, M + 1, last - M))
n0, k0 = allc[0][0], allc[0][1]
L.append("  have h0 : steps %s %d %d = true := %s_%d" % (S, n0, k0, P, n0))
for j, (n, k, h) in enumerate(allc[1:], 1):
  L.append("  have h%d : steps %s %d %d = true := steps_join h%d %s_%d rfl rfl" % (j, S, M + 1, k0 + k, j - 1, P, n))
  k0 += k
assert k0 == last - M
L.append("  exact h%d" % (len(allc) - 1))
L += ["", "end E13Lrat", ""]
open("E13Lrat/Steps%s.lean" % m, "w").write("\n".join(L))
print("M", M, "last", last, "additions", len(hints), "hints", sum(hints), "chunks", len(chunks),
      "modules", len(mods), " ".join(names))
