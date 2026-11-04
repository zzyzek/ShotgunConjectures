import OpenProblemsLib

/-
OEIS A182085 (Mathlib). Conjecture (Coman 2012): (30k+7)(60k+13)(150k+31) is a Carmichael
number if its three factors are all prime (k ≥ 0). README result: true.

Main theorem `A182085_main`: for every natural k, if 30k+7, 60k+13 and 150k+31 are prime
then their product is a Carmichael number (Mathlib `Nat.IsCarmichael`). Proof: Korselt's
criterion (Mathlib `Nat.isCarmichael_iff_korselt`, via `isCarmichael_of_factors`): the
factors are distinct primes and f − 1 divides N − 1 for each factor f by an explicit
polynomial identity (checked by `ring`).

Outside Lean: nothing. (Generated from certificate/A182085_mathlib.lean.in by
tools/lean_expand.py and tools/family_lean.py.)
-/

open OpenProblemsLib

theorem A182085_main (n : ℕ) (h1 : (30 * n + 7).Prime) (h2 : (60 * n + 13).Prime) (h3 : (150 * n + 31).Prime) :
    ((30 * n + 7) * (60 * n + 13) * (150 * n + 31)).IsCarmichael := by
  apply isCarmichael_of_factors _ [30 * n + 7, 60 * n + 13, 150 * n + 31]
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
    · refine dvd_sub_one_of_eq (Q := 9000 * n ^ 2 + 4110 * n + 470) ?_
      rw [show 30 * n + 7 - 1 = 30 * n + 6 by omega]
      ring
    · refine dvd_sub_one_of_eq (Q := 4500 * n ^ 2 + 2055 * n + 235) ?_
      rw [show 60 * n + 13 - 1 = 60 * n + 12 by omega]
      ring
    · refine dvd_sub_one_of_eq (Q := 1800 * n ^ 2 + 822 * n + 94) ?_
      rw [show 150 * n + 31 - 1 = 150 * n + 30 by omega]
      ring
