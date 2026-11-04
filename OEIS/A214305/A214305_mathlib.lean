/-
OEIS A214305, Mathlib proof.

A214305: Fermat pseudoprimes to base 2 (Poulet numbers) with two prime
factors. Conjecture 2 (Coman, 2012): any Poulet number p2 divisible by d can
be written as (p1 - d)·m + d with m a positive integer, if there is a smaller
Poulet number p1 with two prime factors divisible by d. Poulet number is
Mathlib's `Nat.FermatPsp n 2`.

Main theorem `A214305_main` (conjecture 2 fails under each reading of d):
* d any prime dividing both: p1 = 341 = 11·31, p2 = 561, d = 11 is a
  counterexample (no m > 0 with 561 = (341 - 11)·m + 11);
* d the largest prime factor of p1: p1 = 23377 = 97·241, p2 = 34945, d = 241
  is a counterexample, and every Poulet number p1 < 34945 divisible by 241
  is 23377, so p2 = 34945 fails for every qualifying p1 (the reading
  "for some qualifying p1");
* also p1 = 5461 = 43·127, p2 = 55245, d = 127.
This is the README result (conjectures 1 and 3, "infinitely many", are not
addressed). Nothing is outside Lean.
-/
import Mathlib
import OpenProblemsLib.Fermat

open OpenProblemsLib

/-- p2 = (p1 - d)·m + d for some positive integer m. -/
def A214305_form (p1 p2 d : ℕ) : Prop := ∃ m : ℕ, 0 < m ∧ p2 = (p1 - d) * m + d

theorem A214305_not_form (p1 p2 d : ℕ) (h : (p2 - d) % (p1 - d) ≠ 0) :
    ¬ A214305_form p1 p2 d := by
  rintro ⟨m, -, hm⟩
  apply h
  rw [hm, Nat.add_sub_cancel, Nat.mul_mod_right]

theorem A214305_only_23377 : ∀ p1 < 34945, p1.FermatPsp 2 → 241 ∣ p1 → p1 = 23377 := by
  have hc : (List.range 145).all
      (fun k => k < 2 || k == 97 || powMod 2 (241 * k - 1) (241 * k) != 1) = true := by
    decide +kernel
  rintro p1 hp1 hpsp ⟨k, rfl⟩
  have hk : k < 145 := by omega
  have := List.all_eq_true.1 hc k (List.mem_range.2 hk)
  simp only [Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq, bne_iff_ne, ne_eq] at this
  rcases this with (h | h) | h
  · interval_cases k
    · exact absurd hpsp.2.2 (by norm_num)
    · exact absurd hpsp.2.1 (by norm_num)
  · subst h; rfl
  · by_cases hk2 : k < 2
    · interval_cases k
      · exact absurd hpsp.2.2 (by norm_num)
      · exact absurd hpsp.2.1 (by norm_num)
    · exact absurd hpsp (not_fermatPsp_of_powMod _ 2 (by norm_num) (by omega) h)

theorem A214305_main :
    -- d any common prime
    ((341 : ℕ).FermatPsp 2 ∧ 341 = 11 * 31 ∧ (11 : ℕ).Prime ∧ (31 : ℕ).Prime ∧
      (561 : ℕ).FermatPsp 2 ∧ 341 < 561 ∧ 11 ∣ 561 ∧ ¬ A214305_form 341 561 11) ∧
    -- d the largest prime factor of p1
    ((23377 : ℕ).FermatPsp 2 ∧ 23377 = 97 * 241 ∧ (97 : ℕ).Prime ∧ (241 : ℕ).Prime ∧
      (34945 : ℕ).FermatPsp 2 ∧ 23377 < 34945 ∧ 241 ∣ 34945 ∧ ¬ A214305_form 23377 34945 241 ∧
      ∀ p1 < 34945, p1.FermatPsp 2 → 241 ∣ p1 → p1 = 23377) ∧
    ((5461 : ℕ).FermatPsp 2 ∧ 5461 = 43 * 127 ∧ (43 : ℕ).Prime ∧ (127 : ℕ).Prime ∧
      (55245 : ℕ).FermatPsp 2 ∧ 5461 < 55245 ∧ 127 ∣ 55245 ∧ ¬ A214305_form 5461 55245 127) := by
  refine ⟨⟨fermatPsp_of_pspCheck _ _ 11 (by decide +kernel), by norm_num, by norm_num, by norm_num,
      fermatPsp_of_pspCheck _ _ 3 (by decide +kernel), by norm_num, by norm_num,
      A214305_not_form _ _ _ (by norm_num)⟩,
    ⟨fermatPsp_of_pspCheck _ _ 97 (by decide +kernel), by norm_num, by norm_num, by norm_num,
      fermatPsp_of_pspCheck _ _ 5 (by decide +kernel), by norm_num, by norm_num,
      A214305_not_form _ _ _ (by norm_num), A214305_only_23377⟩,
    ⟨fermatPsp_of_pspCheck _ _ 43 (by decide +kernel), by norm_num, by norm_num, by norm_num,
      fermatPsp_of_pspCheck _ _ 3 (by decide +kernel), by norm_num, by norm_num,
      A214305_not_form _ _ _ (by norm_num)⟩⟩
