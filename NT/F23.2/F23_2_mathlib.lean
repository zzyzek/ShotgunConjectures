import Mathlib

/-
NT-F23.2 (Mathlib). Guy F23: Erdős observes that n! = 2^a + 2^b only when n = 1, 2, 3, 4 and 5
(sign as printed; possibly an OCR loss of ±). README result: for "+" the solutions are exactly
n = 2, 3, 4; for "−", n! = 2^a − 2^b, exactly n = 1, …, 5.

Main theorem `F23_2_main`, for every n : ℕ (Mathlib `Nat.factorial`, ℕ subtraction):
* (∃ a b, n ! = 2^a + 2^b) ↔ n ∈ {2, 3, 4};
* (∃ a b, n ! = 2^a - 2^b) ↔ n ≤ 5.
In the "−" statement n = 0 is also a solution (0! = 1 = 2 − 1); for n ≥ 1 it says exactly
n = 1, …, 5 as in the README. ℕ subtraction is harmless: 2^a − 2^b = 0 < n! when a ≤ b.

Proof. "+": 2^a + 2^b is never divisible by 7 (powers of 2 are 1, 2, 4 mod 7), so n ≤ 6; then
a, b < 10 and a finite check (as in the core file F23_2.lean). "−": n! = 2^b (2^c − 1) with
c ≥ 1. For n ≥ 18 let k = n / 3 ≥ 6. 3^k ∣ n! (3^k ∣ (3k)!), so 3^k ∣ 2^c − 1; 3 ∣ 2^c − 1
forces c = 2d, and lifting the exponent (`padicValNat.pow_sub_pow`: v₃(4^d − 1) = 1 + v₃(d))
gives 3^(k−1) ∣ d. Then 2^(2·3^(k−1)) ≤ 2^c ≤ n! + 1 ≤ 2^(n·n), so 2·3^(k−1) ≤ n·n ≤ (3k+2)^2,
false for k ≥ 6. For 6 ≤ n ≤ 17, a ≤ 49 and a finite check by `decide`.

Outside Lean: nothing.
-/

open Nat

/-! ### The "+" reading -/

theorem F23_pow2_mod7 (a : ℕ) : 2 ^ a % 7 = 1 ∨ 2 ^ a % 7 = 2 ∨ 2 ^ a % 7 = 4 := by
  induction a with
  | zero => decide
  | succ k ih =>
    rw [Nat.pow_succ, Nat.mul_mod]
    rcases ih with h | h | h <;> rw [h] <;> decide

theorem F23_sum_mod7 (a b : ℕ) : (2 ^ a + 2 ^ b) % 7 ≠ 0 := by
  rw [Nat.add_mod]
  rcases F23_pow2_mod7 a with h | h | h <;> rcases F23_pow2_mod7 b with h' | h' | h' <;>
    rw [h, h'] <;> decide

theorem F23_plus_small : ∀ n ≤ 6, ∀ a < 10, ∀ b < 10,
    (n ! = 2 ^ a + 2 ^ b → n = 2 ∨ n = 3 ∨ n = 4) := by
  decide +kernel

theorem F23_plus (n a b : ℕ) (h : n ! = 2 ^ a + 2 ^ b) : n = 2 ∨ n = 3 ∨ n = 4 := by
  by_cases h7 : 7 ≤ n
  · have hd : 7 ∣ n ! := Nat.dvd_factorial (by norm_num) h7
    rw [h] at hd
    exact absurd (Nat.mod_eq_zero_of_dvd hd) (F23_sum_mod7 a b)
  · have hle : n ! ≤ 720 := by
      have : n ! ≤ 6 ! := Nat.factorial_le (by omega)
      simpa [Nat.factorial] using this
    have hA : 2 ^ a ≤ n ! := h ▸ Nat.le_add_right _ _
    have hB : 2 ^ b ≤ n ! := h ▸ Nat.le_add_left _ _
    have ha : a < 10 := by
      by_contra hc
      have : 2 ^ 10 ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have hb : b < 10 := by
      by_contra hc
      have : 2 ^ 10 ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    exact F23_plus_small n (by omega) a ha b hb h

/-! ### The "−" reading -/

theorem F23_three_pow_dvd (k : ℕ) : 3 ^ k ∣ (3 * k) ! := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show 3 * (k + 1) = (3 * k + 2) + 1 by ring, Nat.factorial_succ,
      show 3 * k + 2 = (3 * k + 1) + 1 by ring, Nat.factorial_succ, Nat.factorial_succ,
      pow_succ]
    have h3 : 3 ∣ 3 * k + 1 + 1 + 1 := ⟨k + 1, by ring⟩
    rw [mul_comm (3 ^ k) 3]
    exact Nat.mul_dvd_mul h3 (Dvd.dvd.mul_left (Dvd.dvd.mul_left ih _) _)

theorem F23_poly_lt (k : ℕ) (hk : 6 ≤ k) : (3 * k + 2) * (3 * k + 2) < 2 * 3 ^ (k - 1) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 6 := ⟨k - 6, by omega⟩
  rw [show j + 6 - 1 = j + 5 by omega]
  induction j with
  | zero => norm_num
  | succ j ih =>
    have h := ih (by omega)
    rw [pow_succ]
    nlinarith

theorem F23_fact_lt (n : ℕ) (hn : 1 ≤ n) : n ! < 2 ^ (n * n) := by
  calc n ! ≤ n ^ n := Nat.factorial_le_pow n
    _ < (2 ^ n) ^ n := Nat.pow_lt_pow_left Nat.lt_two_pow_self (by omega)
    _ = 2 ^ (n * n) := by rw [← pow_mul]

theorem F23_minus_large (n a b : ℕ) (hn : 18 ≤ n) (h : n ! = 2 ^ a - 2 ^ b) : False := by
  have hpos := Nat.factorial_pos n
  have hba : b < a := by
    by_contra hc
    have : 2 ^ a ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  obtain ⟨c, rfl⟩ : ∃ c, a = b + c := ⟨a - b, by omega⟩
  have hfac : n ! = 2 ^ b * (2 ^ c - 1) := by
    rw [h, pow_add, Nat.mul_sub_one]
  set k := n / 3 with hk
  have hk6 : 6 ≤ k := by omega
  have h3k : 3 ^ k ∣ n ! :=
    Nat.dvd_trans (F23_three_pow_dvd k) (Nat.factorial_dvd_factorial (by omega))
  rw [hfac] at h3k
  have hcop : Nat.Coprime (3 ^ k) (2 ^ b) :=
    Nat.Coprime.pow _ _ (by norm_num)
  have h3c : 3 ^ k ∣ 2 ^ c - 1 := hcop.dvd_of_dvd_mul_left h3k
  -- c is even, since 3 ∣ 2^c - 1.
  --
  have h3 : 3 ∣ 2 ^ c - 1 :=
    Nat.dvd_trans (dvd_pow_self 3 (by omega)) h3c
  have hc1 : 1 ≤ 2 ^ c := Nat.one_le_two_pow
  obtain ⟨d, rfl⟩ : ∃ d, c = 2 * d := by
    rcases Nat.even_or_odd c with ⟨d, hd⟩ | ⟨d, hd⟩
    · exact ⟨d, by omega⟩
    · exfalso
      have e : 2 ^ c = 2 * 4 ^ d := by
        rw [hd, pow_succ, pow_mul]; norm_num; ring
      have h4 : 4 ^ d % 3 = 1 := by
        rw [Nat.pow_mod]; norm_num
      have := Nat.mod_eq_zero_of_dvd h3
      omega
  have hd0 : d ≠ 0 := by
    rintro rfl
    simp at hfac
    omega
  have e4 : 2 ^ (2 * d) = 4 ^ d := by rw [pow_mul]; norm_num
  rw [e4] at h3c hfac
  -- Lifting the exponent: v₃(4^d − 1) = 1 + v₃(d).
  --
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hlte := padicValNat.pow_sub_pow (p := 3) (x := 4) (y := 1) (by decide) (by norm_num)
    (by norm_num) (by norm_num) hd0
  rw [one_pow, show (4 : ℕ) - 1 = 3 by norm_num, padicValNat_self] at hlte
  have h4d0 : 4 ^ d - 1 ≠ 0 := by
    have : 4 ≤ 4 ^ d := by
      calc 4 = 4 ^ 1 := by norm_num
        _ ≤ 4 ^ d := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hkv : k ≤ padicValNat 3 (4 ^ d - 1) := (padicValNat_dvd_iff_le h4d0).mp h3c
  have hdv : 3 ^ (k - 1) ∣ d := (padicValNat_dvd_iff_le hd0).mpr (by omega)
  have hdle : 3 ^ (k - 1) ≤ d := Nat.le_of_dvd (by omega) hdv
  -- Size: 2^(2·3^(k−1)) ≤ 4^d ≤ n! + 1 ≤ 2^(n·n).
  --
  have hb1 : 1 ≤ 2 ^ b := Nat.one_le_two_pow
  have hsz : 4 ^ d ≤ n ! + 1 := by
    have : 4 ^ d - 1 ≤ 2 ^ b * (4 ^ d - 1) := Nat.le_mul_of_pos_left _ (by omega)
    omega
  have hup := F23_fact_lt n (by omega)
  have hchain : 2 ^ (2 * 3 ^ (k - 1)) ≤ 2 ^ (n * n) := by
    calc 2 ^ (2 * 3 ^ (k - 1)) = 4 ^ (3 ^ (k - 1)) := by rw [pow_mul]; norm_num
      _ ≤ 4 ^ d := Nat.pow_le_pow_right (by norm_num) hdle
      _ ≤ 2 ^ (n * n) := by omega
  have hexp : 2 * 3 ^ (k - 1) ≤ n * n := (Nat.pow_le_pow_iff_right (by norm_num)).mp hchain
  have hn3 : n ≤ 3 * k + 2 := by omega
  have := F23_poly_lt k hk6
  have : n * n ≤ (3 * k + 2) * (3 * k + 2) := Nat.mul_le_mul hn3 hn3
  omega

theorem F23_minus_mid : ∀ n, 6 ≤ n → n ≤ 17 → ∀ a < 50, ∀ b < 50, n ! ≠ 2 ^ a - 2 ^ b := by
  decide +kernel

theorem F23_minus (n a b : ℕ) (h : n ! = 2 ^ a - 2 ^ b) : n ≤ 5 := by
  by_contra hn
  by_cases h18 : 18 ≤ n
  · exact F23_minus_large n a b h18 h
  · have hpos := Nat.factorial_pos n
    have hba : b < a := by
      by_contra hc
      have : 2 ^ a ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have hle : n ! ≤ 17 ! := Nat.factorial_le (by omega)
    have h17 : (17 ! : ℕ) < 2 ^ 49 := by decide
    have ha : a < 50 := by
      by_contra hc
      obtain ⟨e, rfl⟩ : ∃ e, a = e + 1 := ⟨a - 1, by omega⟩
      have h1 : 2 ^ b ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) (by omega)
      have h2 : 2 ^ 49 ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) (by omega)
      rw [pow_succ] at h
      omega
    exact F23_minus_mid n (by omega) (by omega) a ha b (by omega) h

theorem F23_2_main : ∀ n : ℕ,
    ((∃ a b : ℕ, n ! = 2 ^ a + 2 ^ b) ↔ n = 2 ∨ n = 3 ∨ n = 4) ∧
    ((∃ a b : ℕ, n ! = 2 ^ a - 2 ^ b) ↔ n ≤ 5) := by
  intro n
  constructor
  · constructor
    · rintro ⟨a, b, h⟩; exact F23_plus n a b h
    · rintro (rfl | rfl | rfl)
      · exact ⟨0, 0, by decide⟩
      · exact ⟨2, 1, by decide⟩
      · exact ⟨4, 3, by decide⟩
  · constructor
    · rintro ⟨a, b, h⟩; exact F23_minus n a b h
    · intro hn
      interval_cases n
      · exact ⟨1, 0, by decide⟩
      · exact ⟨1, 0, by decide⟩
      · exact ⟨2, 1, by decide⟩
      · exact ⟨3, 1, by decide⟩
      · exact ⟨5, 3, by decide⟩
      · exact ⟨7, 3, by decide⟩
