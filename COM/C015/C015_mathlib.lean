import OpenProblemsLib

/-
COM-C015 (Mathlib). Coman's conjecture 15: (330n+7)(660n+13)(990n+19)(1980n+37) is a Carmichael number whenever its factors are all prime.
README result: true.

Main theorem `C015_main`: for every natural n, if all the factors are prime then their
product is a Carmichael number (Mathlib `Nat.IsCarmichael`). 
Proof: Korselt's criterion (Mathlib `Nat.isCarmichael_iff_korselt`, via
`isCarmichael_of_factors`): the factors are distinct primes and f − 1 divides N − 1 for
each factor f by an explicit polynomial identity (checked by `ring`).

Outside Lean: nothing. (Generated from certificate/C015_mathlib.lean.in by
tools/lean_expand.py and tools/family_lean.py.)
-/

open OpenProblemsLib

theorem C015_main (n : ℕ) (h1 : (330 * n + 7).Prime) (h2 : (660 * n + 13).Prime) (h3 : (990 * n + 19).Prime) (h4 : (1980 * n + 37).Prime) :
    ((330 * n + 7) * (660 * n + 13) * (990 * n + 19) * (1980 * n + 37)).IsCarmichael := by
  apply isCarmichael_of_factors _ [330 * n + 7, 660 * n + 13, 990 * n + 19, 1980 * n + 37]
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro p (rfl | rfl | rfl | rfl)
    exacts [h1, h2, h3, h4]
  · simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
      List.nodup_nil, not_false_eq_true, and_true]
    omega
  · simp only [List.prod_cons, List.prod_nil, mul_one, mul_assoc]
  · simp
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro p (rfl | rfl | rfl | rfl)
    · refine dvd_sub_one_of_eq (Q := 1293732000 * n ^ 3 + 78408000 * n ^ 2 + 1583670 * n + 10662) ?_
      rw [show 330 * n + 7 - 1 = 330 * n + 6 by omega]
      ring
    · refine dvd_sub_one_of_eq (Q := 646866000 * n ^ 3 + 39204000 * n ^ 2 + 791835 * n + 5331) ?_
      rw [show 660 * n + 13 - 1 = 660 * n + 12 by omega]
      ring
    · refine dvd_sub_one_of_eq (Q := 431244000 * n ^ 3 + 26136000 * n ^ 2 + 527890 * n + 3554) ?_
      rw [show 990 * n + 19 - 1 = 990 * n + 18 by omega]
      ring
    · refine dvd_sub_one_of_eq (Q := 215622000 * n ^ 3 + 13068000 * n ^ 2 + 263945 * n + 1777) ?_
      rw [show 1980 * n + 37 - 1 = 1980 * n + 36 by omega]
      ring
