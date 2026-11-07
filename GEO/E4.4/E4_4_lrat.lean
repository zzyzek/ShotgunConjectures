import OpenProblemsLib.LRAT

/-
GEO-E4.4 (CFG E4, Birch's 8-point question), the SAT part: the CNF written by
`certificate/e44_sat.py` (616 variables, 9800 clauses; `certificate/e44.cnf`, sha256 2d93dac0...)
is unsatisfiable, by the kernel-checked LRAT checker of `OpenProblemsLib.LRAT` on the
CaDiCaL 2.1.3 proof `certificate/e44.lrat` (`cadical --lrat --binary=false e44.cnf e44.lrat`).

Checked here: `birch_cnf_unsat : Unsat birchCnf`, where `birchCnf` is the clause list read from
`certificate/e44.cnf` at elaboration time (`dimacs%`; literal code 2d for DIMACS d, 2d+1 for -d).
Axioms: propext, Classical.choice, Quot.sound.

Not checked here: that `birchCnf` encodes the geometry. Outside Lean: (1) the CNF is the
signotope encoding of `e44_sat.py` (variables = orientations of triples of 8 x-sorted points,
signotope axioms, Tseitin variables for "segment meets open triangle", one clause per partition);
(2) every 8-point set in general position gives a satisfying assignment: orientations of
x-sorted points form a signotope, and "segment pq meets the open triangle abc" is equivalent to
"p or q strictly inside, or pq properly crosses an edge". Check from the repo root (relative paths).
-/

open OpenProblemsLib.LRAT

/-- The 9800 clauses of `certificate/e44.cnf`. -/
noncomputable def birchCnf : List (List Nat) := dimacs% "GEO/E4.4/certificate/e44.cnf"

/-- Untrusted clause store: the CNF, then the LRAT additions. -/
noncomputable def store : T :=
  lratStore% "GEO/E4.4/certificate/e44.cnf" "GEO/E4.4/certificate/e44.lrat"

theorem birch_len : birchCnf.length = 9800 := by decide +kernel

theorem birch_store : chkF store birchCnf 1 = true := by decide +kernel

theorem birch_last : lastEmpty store 10425 = true := by decide +kernel

theorem s9801 : steps store 9801 225 = true := by decide +kernel
theorem s10026 : steps store 10026 170 = true := by decide +kernel
theorem s10196 : steps store 10196 177 = true := by decide +kernel
theorem s10373 : steps store 10373 53 = true := by decide +kernel

theorem birch_steps : steps store 9801 625 = true := by
  have h0 : steps store 9801 225 = true := s9801
  have h1 : steps store 9801 395 = true := steps_join h0 s10026 rfl rfl
  have h2 : steps store 9801 572 = true := steps_join h1 s10196 rfl rfl
  have h3 : steps store 9801 625 = true := steps_join h2 s10373 rfl rfl
  exact h3

theorem birch_cnf_unsat : Unsat birchCnf :=
  unsat_of_parts birchCnf store 9800 625 birch_len birch_store (by decide) birch_steps birch_last
