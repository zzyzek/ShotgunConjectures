/-
Guy B41 (Finucane), Mathlib proof.

Iterate f(n) = φ(n) + 1 (primes are fixed points). Main theorems:
- `B41_5_five`: the set of n ≥ 0 whose iterates reach 5 is exactly
  {5, 8, 10, 12};
- `B41_5_seven`: the set of n whose iterates reach 7 is exactly
  {7, 9, 14, 15, 16, 18, 20, 24, 30}.
"The sequence of n ends at q" for a prime q is "some iterate equals q"
(q is a fixed point, so the sequence then stays at q). These are the two
lists of the README result, and both are complete.

Proof: the set reaching q is closed under preimages of f, so by induction
on the number of steps it suffices that φ(n) + 1 lies in the list only for
n in the list. That is a finite check, because n ≤ 2 φ(n)^2 for all n
(`B41_5_le_two_totient_sq`, proved by multiplicative induction; it is the
bound φ(n) ≥ √(n/2) of the README). φ(n) is even for n > 2 (Mathlib `Nat.totient_even`), so only
φ(n) ∈ {4} resp. {6, 8, 14} remain; the finite checks over n < 33 resp.
n < 393 are done by `decide +kernel` with Mathlib's `Nat.totient`.

Not checked: nothing.
-/
import Mathlib

open Nat

theorem B41_5_le_totient_sq (n : ℕ) :
    n ≤ (if 2 ∣ n then 2 else 1) * φ n ^ 2 := by
  induction n using Nat.recOnPosPrimePosCoprime with
  | zero => simp
  | one => simp
  | prime_pow p k hp hk =>
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [totient_prime_pow_succ hp]
    have h1 : 1 ≤ p ^ j := Nat.one_le_pow _ _ hp.pos
    rcases hp.eq_two_or_odd' with rfl | hodd
    · rw [ite_eq_left (dvd_pow_self 2 (by omega))]
      have : 2 ^ j ≤ 2 ^ j * 2 ^ j := Nat.le_mul_of_pos_right _ (by positivity)
      calc 2 ^ (j + 1) = 2 * 2 ^ j := by ring
        _ ≤ 2 * (2 ^ j * 2 ^ j) := by omega
        _ = 2 * (2 ^ j * (2 - 1)) ^ 2 := by ring
    · have hp3 : 3 ≤ p := by
        have := hp.two_le
        rcases hodd with ⟨r, hr⟩
        omega
      have hq : p ≤ (p - 1) ^ 2 := by
        obtain ⟨q, rfl⟩ : ∃ q, p = q + 3 := ⟨p - 3, by omega⟩
        rw [show q + 3 - 1 = q + 2 by omega]
        nlinarith
      have hc : 1 ≤ (if 2 ∣ p ^ (j + 1) then 2 else 1) := by split_ifs <;> omega
      calc p ^ (j + 1) = p ^ j * p := by ring
        _ ≤ p ^ j * (p ^ j * (p - 1) ^ 2) := by
          apply Nat.mul_le_mul_left
          nlinarith
        _ = (p ^ j * (p - 1)) ^ 2 := by ring
        _ ≤ _ := Nat.le_mul_of_pos_left _ hc
  | coprime a b ha hb hab iha ihb =>
    rw [totient_mul hab]
    have hc : (if 2 ∣ a then 2 else 1) * (if 2 ∣ b then 2 else 1) =
        (if 2 ∣ a * b then 2 else 1) := by
      by_cases h2a : 2 ∣ a
      · by_cases h2b : 2 ∣ b
        · exfalso
          have := Nat.dvd_gcd h2a h2b
          rw [hab] at this
          omega
        · rw [ite_eq_left h2a, ite_eq_right h2b, ite_eq_left (h2a.mul_right b)]
      · by_cases h2b : 2 ∣ b
        · rw [ite_eq_right h2a, ite_eq_left h2b, ite_eq_left (h2b.mul_left a)]
        · rw [ite_eq_right h2a, ite_eq_right h2b,
            ite_eq_right (fun h => (Nat.prime_two.dvd_mul.mp h).elim h2a h2b)]
    rw [← hc]
    calc a * b ≤ ((if 2 ∣ a then 2 else 1) * φ a ^ 2) * ((if 2 ∣ b then 2 else 1) * φ b ^ 2) :=
          Nat.mul_le_mul iha ihb
      _ = _ := by ring

theorem B41_5_le_two_totient_sq (n : ℕ) : n ≤ 2 * φ n ^ 2 := by
  have := B41_5_le_totient_sq n
  split_ifs at this <;> nlinarith

/-- Finucane's map. -/
def B41_5_f (n : ℕ) : ℕ := φ n + 1

theorem B41_5_even (n : ℕ) (h : 2 < φ n) : ∃ r, φ n = r + r := by
  have hn : 2 < n := lt_of_lt_of_le h (totient_le n)
  exact totient_even hn

theorem B41_5_pre5 (n : ℕ)
    (h : B41_5_f n = 5 ∨ B41_5_f n = 8 ∨ B41_5_f n = 10 ∨ B41_5_f n = 12) :
    n = 5 ∨ n = 8 ∨ n = 10 ∨ n = 12 := by
  unfold B41_5_f at h
  obtain ⟨r, hr⟩ := B41_5_even n (by omega)
  have h4 : φ n = 4 := by omega
  have hn : n < 33 := by
    have := B41_5_le_two_totient_sq n
    rw [h4] at this
    omega
  have key : ∀ m < 33, φ m = 4 → m = 5 ∨ m = 8 ∨ m = 10 ∨ m = 12 := by decide +kernel
  exact key n hn h4

theorem B41_5_pre7 (n : ℕ)
    (h : B41_5_f n = 7 ∨ B41_5_f n = 9 ∨ B41_5_f n = 14 ∨ B41_5_f n = 15 ∨
      B41_5_f n = 16 ∨ B41_5_f n = 18 ∨ B41_5_f n = 20 ∨ B41_5_f n = 24 ∨ B41_5_f n = 30) :
    n = 7 ∨ n = 9 ∨ n = 14 ∨ n = 15 ∨ n = 16 ∨ n = 18 ∨ n = 20 ∨ n = 24 ∨ n = 30 := by
  unfold B41_5_f at h
  obtain ⟨r, hr⟩ := B41_5_even n (by omega)
  have h3 : φ n = 6 ∨ φ n = 8 ∨ φ n = 14 := by omega
  have hn : n < 393 := by
    have := B41_5_le_two_totient_sq n
    rcases h3 with h3 | h3 | h3 <;> rw [h3] at this <;> omega
  have key : ∀ m < 393, (φ m = 6 ∨ φ m = 8 ∨ φ m = 14) →
      m = 7 ∨ m = 9 ∨ m = 14 ∨ m = 15 ∨ m = 16 ∨ m = 18 ∨ m = 20 ∨ m = 24 ∨ m = 30 := by
    decide +kernel
  exact key n hn h3

theorem B41_5_five :
    {n : ℕ | ∃ t, B41_5_f^[t] n = 5} = {5, 8, 10, 12} := by
  ext n
  simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨t, ht⟩
    induction t generalizing n with
    | zero => exact Or.inl ht
    | succ t ih =>
      rw [Function.iterate_succ_apply] at ht
      exact B41_5_pre5 n (ih _ ht)
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨0, rfl⟩
    all_goals exact ⟨1, by decide +kernel⟩

theorem B41_5_seven :
    {n : ℕ | ∃ t, B41_5_f^[t] n = 7} = {7, 9, 14, 15, 16, 18, 20, 24, 30} := by
  ext n
  simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨t, ht⟩
    induction t generalizing n with
    | zero => exact Or.inl ht
    | succ t ih =>
      rw [Function.iterate_succ_apply] at ht
      exact B41_5_pre7 n (ih _ ht)
  · rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    · exact ⟨0, rfl⟩
    · exact ⟨1, by decide +kernel⟩
    · exact ⟨1, by decide +kernel⟩
    · exact ⟨2, by decide +kernel⟩
    · exact ⟨2, by decide +kernel⟩
    · exact ⟨1, by decide +kernel⟩
    · exact ⟨2, by decide +kernel⟩
    · exact ⟨2, by decide +kernel⟩
    · exact ⟨2, by decide +kernel⟩
