import OpenProblemsLib

/-
COM-C016 (Mathlib). Coman's conjecture 16: (30n−7)(90n−23)(300n−79) is a Carmichael number whenever its factors are all prime.
README result: true.

Main theorem `C016_main`: for every natural n, if all the factors are prime then their
product is a Carmichael number (Mathlib `Nat.IsCarmichael`). The factors with a negative constant use natural subtraction; for n = 0 they are 0, which is not prime, so the hypotheses exclude n = 0, matching the stated range n ≥ 1.
Proof: Korselt's criterion (Mathlib `Nat.isCarmichael_iff_korselt`, via
`isCarmichael_of_factors`): the factors are distinct primes and f − 1 divides N − 1 for
each factor f by an explicit polynomial identity (checked by `ring`).

Outside Lean: nothing. (Generated from certificate/C016_mathlib.lean.in by
tools/lean_expand.py and tools/family_lean.py.)
-/

open OpenProblemsLib

theorem C016_main (n : ℕ) (h1 : (30 * n - 7).Prime) (h2 : (90 * n - 23).Prime) (h3 : (300 * n - 79).Prime) :
    ((30 * n - 7) * (90 * n - 23) * (300 * n - 79)).IsCarmichael := by
  have l1 := h1.two_le
  have l2 := h2.two_le
  have l3 := h3.two_le
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have e1 : 30 * (k + 1) - 7 = 30 * k + 23 := by omega
  have e2 : 90 * (k + 1) - 23 = 90 * k + 67 := by omega
  have e3 : 300 * (k + 1) - 79 = 300 * k + 221 := by omega
  rw [e1] at h1
  rw [e2] at h2
  rw [e3] at h3
  rw [e1, e2, e3]
  apply isCarmichael_of_factors _ [30 * k + 23, 90 * k + 67, 300 * k + 221]
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
    · refine dvd_sub_one_of_eq (Q := 27000 * k ^ 2 + 40890 * k + 15480) ?_
      rw [show 30 * k + 23 - 1 = 30 * k + 22 by omega]
      ring
    · refine dvd_sub_one_of_eq (Q := 9000 * k ^ 2 + 13630 * k + 5160) ?_
      rw [show 90 * k + 67 - 1 = 90 * k + 66 by omega]
      ring
    · refine dvd_sub_one_of_eq (Q := 2700 * k ^ 2 + 4089 * k + 1548) ?_
      rw [show 300 * k + 221 - 1 = 300 * k + 220 by omega]
      ring
