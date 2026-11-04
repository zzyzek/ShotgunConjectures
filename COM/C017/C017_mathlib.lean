import OpenProblemsLib

/-
COM-C017 (Mathlib). Coman's conjecture 17: (30n+13)(90n+37)(150n+61) is a Carmichael number whenever its factors are all prime.
README result: true.

Main theorem `C017_main`: for every natural n, if all the factors are prime then their
product is a Carmichael number (Mathlib `Nat.IsCarmichael`). 
Proof: Korselt's criterion (Mathlib `Nat.isCarmichael_iff_korselt`, via
`isCarmichael_of_factors`): the factors are distinct primes and f − 1 divides N − 1 for
each factor f by an explicit polynomial identity (checked by `ring`).

Outside Lean: nothing. (Generated from certificate/C017_mathlib.lean.in by
tools/lean_expand.py and tools/family_lean.py.)
-/

open OpenProblemsLib

theorem C017_main (n : ℕ) (h1 : (30 * n + 13).Prime) (h2 : (90 * n + 37).Prime) (h3 : (150 * n + 61).Prime) :
    ((30 * n + 13) * (90 * n + 37) * (150 * n + 61)).IsCarmichael := by
  apply isCarmichael_of_factors _ [30 * n + 13, 90 * n + 37, 150 * n + 61]
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro p (rfl | rfl | rfl)
    exacts [h1, h2, h3]
  · simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
      List.nodup_nil, not_false_eq_true, and_true]
    omega
  · simp only [List.prod_cons, List.prod_nil, mul_one, mul_assoc]
  · simp
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro p (rfl | rfl | rfl)
    · refine dvd_sub_one_of_eq (Q := 13500 * n ^ 2 + 11490 * n + 2445) ?_
      rw [show 30 * n + 13 - 1 = 30 * n + 12 by omega]
      ring
    · refine dvd_sub_one_of_eq (Q := 4500 * n ^ 2 + 3830 * n + 815) ?_
      rw [show 90 * n + 37 - 1 = 90 * n + 36 by omega]
      ring
    · refine dvd_sub_one_of_eq (Q := 2700 * n ^ 2 + 2298 * n + 489) ?_
      rw [show 150 * n + 61 - 1 = 150 * n + 60 by omega]
      ring
