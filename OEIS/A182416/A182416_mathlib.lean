import OpenProblemsLib

/-
OEIS-A182416 (Mathlib). Conjecture (Coman 2012): (60k+13)(180k+37)(300k+61) is a Carmichael number if its three factors are all prime (k ≥ 0).
README result: true.

Main theorem `A182416_main`: for every natural n, if all the factors are prime then their
product is a Carmichael number (Mathlib `Nat.IsCarmichael`). 
Proof: Korselt's criterion (Mathlib `Nat.isCarmichael_iff_korselt`, via
`isCarmichael_of_factors`): the factors are distinct primes and f − 1 divides N − 1 for
each factor f by an explicit polynomial identity (checked by `ring`).

Outside Lean: nothing. (Generated from certificate/A182416_mathlib.lean.in by
tools/lean_expand.py and tools/family_lean.py.)
-/

open OpenProblemsLib

theorem A182416_main (n : ℕ) (h1 : (60 * n + 13).Prime) (h2 : (180 * n + 37).Prime) (h3 : (300 * n + 61).Prime) :
    ((60 * n + 13) * (180 * n + 37) * (300 * n + 61)).IsCarmichael := by
  apply isCarmichael_of_factors _ [60 * n + 13, 180 * n + 37, 300 * n + 61]
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
    · refine dvd_sub_one_of_eq (Q := 54000 * n ^ 2 + 22980 * n + 2445) ?_
      rw [show 60 * n + 13 - 1 = 60 * n + 12 by omega]
      ring
    · refine dvd_sub_one_of_eq (Q := 18000 * n ^ 2 + 7660 * n + 815) ?_
      rw [show 180 * n + 37 - 1 = 180 * n + 36 by omega]
      ring
    · refine dvd_sub_one_of_eq (Q := 10800 * n ^ 2 + 4596 * n + 489) ?_
      rw [show 300 * n + 61 - 1 = 300 * n + 60 by omega]
      ring
