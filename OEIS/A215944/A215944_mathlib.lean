import OpenProblemsLib

/-
OEIS A215944 (Fermat pseudoprimes to base 2 with three prime factors divisible
by a smaller Fermat pseudoprime to base 2).  Conjecture (Marius Coman, entry):
the only base-2 Fermat pseudoprimes divisible by a smaller base-2 Fermat
pseudoprime that cannot be written as p*((m+1)*p - m)*((n+1)*p - n), with
m, n, p natural numbers, are multiples of 5461 of the form 5461*(42k - 13).

Counterexample: P = 3048841 = 61 * 151 * 331, divisible by the pseudoprime
49981 = 151 * 331, not a multiple of 5461, and not of the form for ANY
natural p, m, n (no primality or size condition on p, m, n; ℕ subtraction is
harmless since (m+1)p - m = p + m(p-1) for p ≥ 1).

Main theorem `A215944_counterexample`: the conjunction of
* `P_psp`: Nat.FermatPsp 3048841 2 (lib `pspCheck`, kernel powMod);
* `Q_psp`, `Q_dvd`, `Q_lt`: 49981 is a base-2 Fermat pseudoprime, 49981 ∣ P, 49981 < P;
* `not_5461`: ¬ 5461 ∣ 3048841;
* `not_form`: ∀ p m n, p * ((m+1)*p - m) * ((n+1)*p - n) ≠ 3048841
  (p, A, B are divisors of 61*151*331, listed by lib `divisorsList`;
  A ≡ B ≡ p mod p - 1 and A, B ≥ p are checked over all triples by
  `decide +kernel`).
Not checked in this file: that 3048841 is the least counterexample
(certificate/search.py over the Feitsma-Galway list).
-/

open OpenProblemsLib

namespace A215944

theorem P_psp : Nat.FermatPsp 3048841 2 := fermatPsp_of_pspCheck 3048841 2 61 (by decide +kernel)

theorem Q_psp : Nat.FermatPsp 49981 2 := fermatPsp_of_pspCheck 49981 2 151 (by decide +kernel)

theorem Q_dvd : 49981 ∣ 3048841 := ⟨61, by norm_num⟩

theorem Q_lt : 49981 < 3048841 := by norm_num

theorem not_5461 : ¬ 5461 ∣ 3048841 := by decide

theorem sub_eq (p m : ℕ) (hp : 1 ≤ p) : (m + 1) * p - m = p + m * (p - 1) := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  rw [Nat.add_sub_cancel, show (m + 1) * (q + 1) = (q + 1 + m * q) + m by ring]
  omega

theorem key : ∀ x ∈ divisorsList [61, 151, 331], ∀ y ∈ divisorsList [61, 151, 331],
    ∀ z ∈ divisorsList [61, 151, 331], x * y * z = 3048841 → 2 ≤ x → x ≤ y → x ≤ z →
    y % (x - 1) = x % (x - 1) → z % (x - 1) = x % (x - 1) → False := by decide +kernel

theorem not_form (p m n : ℕ) : p * ((m + 1) * p - m) * ((n + 1) * p - n) ≠ 3048841 := by
  intro h
  have hps : ∀ x ∈ [61, 151, 331], x.Prime := by norm_num
  have hprod : [61, 151, 331].prod = 3048841 := by norm_num
  rcases Nat.lt_or_ge p 2 with hp | hp
  · interval_cases p <;> simp at h
  rw [sub_eq p m (by omega), sub_eq p n (by omega)] at h
  have hD : ∀ d, d ∣ 3048841 → d ∈ divisorsList [61, 151, 331] := fun d hd =>
    mem_divisorsList_of_dvd _ hps (hprod ▸ hd)
  refine key p (hD p ⟨_, by rw [← h, mul_assoc]⟩) _ (hD _ ⟨p * (p + n * (p - 1)), by rw [← h]; ring⟩)
    _ (hD _ ⟨p * (p + m * (p - 1)), by rw [← h]; ring⟩) h hp (by omega) (by omega) ?_ ?_
  · exact Nat.add_mul_mod_self_right p m (p - 1)
  · exact Nat.add_mul_mod_self_right p n (p - 1)

theorem A215944_counterexample :
    Nat.FermatPsp 3048841 2 ∧ (∃ d, Nat.FermatPsp d 2 ∧ d ∣ 3048841 ∧ d < 3048841) ∧
    ¬ 5461 ∣ 3048841 ∧ ∀ p m n : ℕ, p * ((m + 1) * p - m) * ((n + 1) * p - n) ≠ 3048841 :=
  ⟨P_psp, ⟨49981, Q_psp, Q_dvd, Q_lt⟩, not_5461, not_form⟩
