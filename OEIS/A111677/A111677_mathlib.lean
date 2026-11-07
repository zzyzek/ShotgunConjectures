/-
OEIS A111677 (Mathlib): row n of A111676 lists the primes "k concatenated with 2n-1" with 1 <= k < 2n-1;
a(n) is the number of them. Conjecture in the entry: a(n) = 0 iff n == 3 (mod 5).

Checked here:
* `A111677_one`: a(1) = 0 although 1 is not 3 mod 5 (row 1 is empty: no k with 1 <= k < 1), so the
  stated "iff" fails at n = 1 (`A111677_misstated`).
* `A111677_zero_of_mod5`: n == 3 (mod 5) implies a(n) = 0, for every n (the "if" direction).
Not checked: the remaining direction (a(n) > 0 for n >= 2, n not 3 mod 5), which is open.
-/
import Mathlib

/-- k concatenated with m in decimal. -/
def A111677_cat (k m : ℕ) : ℕ := k * 10 ^ (Nat.digits 10 m).length + m

/-- A111677(n): number of k with 1 <= k < 2n-1 and k concatenated with 2n-1 prime. -/
def A111677 (n : ℕ) : ℕ :=
  ((Finset.Ico 1 (2 * n - 1)).filter (fun k => Nat.Prime (A111677_cat k (2 * n - 1)))).card

theorem A111677_one : A111677 1 = 0 := by
  simp [A111677]

/-- Main theorem: the stated characterisation fails at n = 1. -/
theorem A111677_misstated : ¬ (∀ n ≥ 1, A111677 n = 0 ↔ n % 5 = 3) := by
  intro h
  have := (h 1 le_rfl).mp A111677_one
  omega

theorem A111677_zero_of_mod5 (n : ℕ) (hn : n % 5 = 3) : A111677 n = 0 := by
  unfold A111677
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro k hk hp
  rw [Finset.mem_Ico] at hk
  have hD : 1 ≤ (Nat.digits 10 (2 * n - 1)).length := by
    rw [Nat.one_le_iff_ne_zero, Ne, List.length_eq_zero_iff, Nat.digits_eq_nil_iff_eq_zero]
    omega
  have h5 : 5 ∣ A111677_cat k (2 * n - 1) := by
    unfold A111677_cat
    apply dvd_add
    · apply Dvd.dvd.mul_left
      obtain ⟨e, he⟩ := Nat.exists_eq_add_of_le hD
      rw [he, pow_add]
      exact Dvd.dvd.mul_right (by norm_num) _
    · omega
  have hgt : 5 < A111677_cat k (2 * n - 1) := by
    unfold A111677_cat
    have : 10 ≤ 10 ^ (Nat.digits 10 (2 * n - 1)).length := by
      calc 10 = 10 ^ 1 := by norm_num
        _ ≤ _ := Nat.pow_le_pow_right (by norm_num) hD
    nlinarith
  exact absurd ((Nat.prime_dvd_prime_iff_eq (by norm_num) hp).mp h5) (by omega)
