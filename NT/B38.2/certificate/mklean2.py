#!/usr/bin/env python3
# Lean file for NT-B38.2: sigma(y) = n! is solvable for N0 <= n <= N1, from witness lines
# "n q^a ..." (search_small.py output).  Witnesses are split into chunks of CH rows, each
# checked by its own kernel declaration.
#
# usage: mklean2.py witnesses.txt N0 N1 CH > B38_2_mathlib.lean
#
import sys
src, N0, N1, CH = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
rows = {}
for l in open(src):
  t = l.split()
  if (len(t) > 1) and (t[1] != "FAIL"):
    rows[int(t[0])] = [tuple(map(int, x.split("^"))) for x in t[1:]]
ns = list(range(N0, N1+1))
assert all(n in rows for n in ns)
chunks = [ns[i:i+CH] for i in range(0, len(ns), CH)]
K = len(chunks)
o = []
o.append(f"""import OpenProblemsLib

/-
NT-B38.2 (Mathlib). Guy B38 (Erdős): is σ(y) = n! solvable for every n ≠ 2?

Main theorem `B38_2_main`: for every n with {N0} ≤ n ≤ {N1} there is y with σ(y) = n!
(σ = Mathlib `ArithmeticFunction.sigma 1`). Alekseyev (J. Integer Seq. 19 (2016), OEIS
A055486) counted the solutions for n ≤ 28.

Proof: for each n an explicit y = ∏ q^a, given as a factor list (table `W`, from
certificate/search_small.py). The kernel checks that the bases are distinct primes (trial
division up to √q, `OpenProblemsLib.ArithFactor.factCheck`) and that ∏ (1 + q + … + q^a) = n!;
`sigma_val` turns the product into σ(y) by multiplicativity. The table is checked in {K} chunks.

Outside Lean: none.
-/

open OpenProblemsLib.ArithFactor ArithmeticFunction



def ok1 (x : ℕ × PF) : Bool := factCheck x.2 && sigF x.2 == x.1.factorial
""")
for k, ch in enumerate(chunks):
  o.append(f"def W{k:02d} : List (ℕ × PF) := [")
  o.append(",\n".join("  (" + str(n) + ", [" + ", ".join(f"({q}, {a})" for q, a in rows[n]) + "])" for n in ch) + "]")
  o.append(f"theorem ok{k:02d} : W{k:02d}.all ok1 = true := by decide +kernel\n")
o.append("def W : List (ℕ × PF) := " + " ++ (".join(f"W{k:02d}" for k in range(K)) + ")"*(K-1))
o.append("")
o.append(f"theorem W_keys : W.map Prod.fst = List.range' {N0} {N1 - N0 + 1} := by decide +kernel")
o.append("")
o.append("theorem W_ok : W.all ok1 = true := by")
o.append("  simp only [W, List.all_append, " + ", ".join(f"ok{k:02d}" for k in range(K)) + ", Bool.and_self]")
o.append(f"""
theorem B38_2_main (n : ℕ) (h0 : {N0} ≤ n) (h1 : n ≤ {N1}) :
    ∃ y, sigma 1 y = n.factorial := by
  have hmem : n ∈ W.map Prod.fst := by
    rw [W_keys, List.mem_range']
    exact ⟨n - {N0}, by omega, by omega⟩
  obtain ⟨⟨m, f⟩, hin, hm⟩ := List.mem_map.mp hmem
  simp only at hm
  subst hm
  have h := List.all_eq_true.mp W_ok _ hin
  simp only [ok1, Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨val f, by rw [sigma_val f (factOK_of_check f h.1)]; exact h.2⟩


""")
print("\n".join(o))
