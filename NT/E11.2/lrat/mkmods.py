#!/usr/bin/env python3
# Write the NT-E11.2 data modules from data/tri171.txt (the solution tuples of the CNF,
# lines "x y z c", in CNF order) and data/c171.cnf / data/c171.lrat:
#   E11Lrat/Tri.lean   : chunk lists Tk of packed tuples x + 256 y + 65536 z + 2^24 c,
#                        L = T00.map dec ++ (T01.map dec ++ ...), chunk validity checks
#   E11Lrat/Store.lean : the clause store S (untrusted)
#   E11Lrat/F.lean     : store begins with cnf 171 L (chunked chkF), ends with the empty clause
# and the LRAT step chunks Q00.. plus Steps.lean (as NT/E13.1/lrat/gen.py).
#
# usage: mkmods.py
#
N   = 171
CH  = 1000
T   = [tuple(map(int, l.split())) for l in open("data/tri171.txt") if l.strip()]
M   = int(open("data/c171.cnf").readline().split()[3])
FIX = N + 6*N + 2 + (N - 1)
assert M == FIX + len(T)
chunks = [T[i:i+CH] for i in range(0, len(T), CH)]
K = len(chunks)

def pack(t):
  x, y, z, c = t
  assert max(x, y, z) < 256
  return x + 256*y + 65536*z + 16777216*c

L = ["import E11Lrat.Cnf", "",
     "/-! # NT-E11.2: the solution tuples used by the CNF (data; validity checked here)",
     "",
     f"`L` lists {len(T)} tuples `(x, y, z, c)` in {K} chunks; each is packed as",
     "`x + 256 y + 65536 z + 2^24 c`. Which tuples are listed is untrusted (any list of valid",
     "tuples gives a CNF that every symmetry-broken colouring satisfies); `L_valid` checks that",
     "every tuple is a solution of x + y + z = w in [1, 171] with `c < 4`. -/", "",
     "namespace E11Lrat", "",
     "def dec (t : Nat) : Nat × Nat × Nat × Nat := (t % 256, t / 256 % 256, t / 65536 % 256, t / 16777216)",
     ""]
for k, ch in enumerate(chunks):
  L.append(f"def T{k:02d} : List Nat := [" + ", ".join(str(pack(t)) for t in ch) + "]")
L.append("")
L.append("def L : List (Nat × Nat × Nat × Nat) :=")
L.append("  " + " ++ (".join(f"T{k:02d}.map dec" for k in range(K)) + ")"*(K-1))
L.append("")
for k in range(K):
  L.append(f"theorem V{k:02d} : (T{k:02d}.map dec).all (validT {N}) = true := by decide +kernel")
L.append("")
L.append(f"theorem L_valid : L.all (validT {N}) = true := by")
L.append("  simp only [L, List.all_append, " + ", ".join(f"V{k:02d}" for k in range(K)) + ", Bool.and_self]")
L += ["", "end E11Lrat", ""]
open("E11Lrat/Tri.lean", "w").write("\n".join(L))

S = ["import OpenProblemsLib.LRAT", "",
     "/-! # NT-E11.2: the clause store (untrusted data)", "",
     f"Entries 1..{M}: the clauses of `data/c171.cnf`; later entries: the additions of",
     "`data/c171.lrat` (CaDiCaL `--lrat --binary=false`, backward-trimmed). Nothing about the data",
     "is trusted: `E11Lrat.F` checks that the first entries are `cnf 171 L`, the step modules check",
     "every later entry by RUP. -/", "",
     "namespace E11Lrat", "", "open OpenProblemsLib.LRAT", "",
     'set_option maxHeartbeats 1000000 in',
     'noncomputable def S : T := lratStore% "NT/E11.2/lrat/data/c171.cnf" "NT/E11.2/lrat/data/c171.lrat"',
     "", "end E11Lrat", ""]
open("E11Lrat/Store.lean", "w").write("\n".join(S))

last = None
for line in open("data/c171.lrat"):
  t = line.split()
  if t and t[1] != "d":
    last = int(t[0])

F = ["import E11Lrat.Tri", "import E11Lrat.Store", "",
     "/-! # NT-E11.2: the store begins with `cnf 171 L` and ends with the empty clause -/", "",
     "namespace E11Lrat", "", "open OpenProblemsLib.LRAT", "",
     f"def P0 : List (List Nat) := alo {N} ++ amo {N} ++ symm {N}"]
for k in range(K):
  F.append(f"def P{k+1} : List (List Nat) := (T{k:02d}.map dec).map triC")
F.append("")
F.append("theorem map_eq : L.map triC = " + " ++ (".join(f"P{k+1}" for k in range(K)) + ")"*(K-1) + " := by")
F.append("  simp only [L, List.map_append]; rfl")
F.append("")
F.append(f"theorem cnf_eq : cnf {N} L = P0 ++ (" + " ++ (".join(f"P{k+1}" for k in range(K)) + ")"*K + " := by")
F.append("  unfold cnf; rw [map_eq]; rfl")
F.append("")
off = [1]
lens = [FIX] + [len(ch) for ch in chunks]
for l in lens:
  off.append(off[-1] + l)
for k in range(K+1):
  F.append(f"theorem len{k} : P{k}.length = {lens[k]} := by decide +kernel")
  F.append(f"theorem chk{k} : chkF S P{k} {off[k]} = true := by decide +kernel")
F.append("")
# Right-nested chain: R_k = P_k ++ (P_{k+1} ++ ...).
#
F.append(f"theorem chain{K} : chkF S P{K} {off[K]} = true := chk{K}")
for k in range(K-1, -1, -1):
  rest = " ++ (".join(f"P{j}" for j in range(k+1, K+1)) + ")"*(K-k-1)
  F.append(f"theorem chain{k} : chkF S (P{k} ++ ({rest})) {off[k]} = true := by")
  F.append(f"  rw [chkF_append, chk{k}, len{k}, Bool.true_and]; exact chain{k+1}")
F.append("")
F.append(f"theorem cnf_length : (cnf {N} L).length = {M} := by")
F.append("  rw [cnf_eq]; simp only [List.length_append, " + ", ".join(f"len{k}" for k in range(K+1)) + "]")
F.append("")
F.append(f"theorem store_cnf : chkF S (cnf {N} L) 1 = true := by")
F.append("  rw [cnf_eq]; exact chain0")
F.append("")
F.append(f"theorem store_last : lastEmpty S {last} = true := by decide +kernel")
F += ["", "end E11Lrat", ""]
open("E11Lrat/F.lean", "w").write("\n".join(F))
print("M", M, "last", last, "chunks", K)
