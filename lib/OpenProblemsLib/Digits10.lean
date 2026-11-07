import Mathlib

/-!
# Base-10 digits: digit sums of concatenations, periodic powers of 10, repunits

Lemmas for arguments that build a decimal number from blocks of digits and need its digit sum
or its residue mod `n`. Digit lists are Mathlib's `Nat.digits 10` (least significant digit
first); the digit sum is `(Nat.digits 10 x).sum`.

Definitions.
* `rp Y k` : the list `Y ++ Y ++ ... ++ Y` (`k` copies).
* `rep B k` : `1 + B + ... + B^(k-1)`; for `B = 10^L` the number whose base-`10^L` digits are
  `k` ones (the base-`10^L` repunit).

Main results.
* `digitSum_add` : if `a < 10^m` then the digit sum of `a + 10^m b` is that of `a` plus that of `b`.
* `digitSum_le` : the digit sum of `x` is at most `9 + x / 10`.
* `pow_period` : the powers of 10 are eventually periodic mod `n`: `10^(i+P) ≡ 10^i (mod n)`
  for some `i` and `P > 0`.
* `pow_period_mul` : such a period may be added any number of times to any exponent `≥ i`.
* `ofDigits_rp` : the number with digits `rp Y k` is `ofDigits Y * rep (10^|Y|) k`.
* `rep_mul` : `rep B k * (B - 1) + 1 = B^k`.
* `dvd_rep` : if `gcd(m, 10) = 1` and `L ≥ 1`, `m` divides the base-`10^L` repunit with
  `j + 2` ones for some `j`.

Used by OEIS A077739/A077740 and A084043/A084044.
-/

namespace OpenProblemsLib.Digits10

open Nat

/-- Placing `b` above `m` decimal places that hold `a < 10^m` adds the digit sums. -/
theorem digitSum_add (m a b : ℕ) (ha : a < 10 ^ m) :
    (digits 10 (a + 10 ^ m * b)).sum = (digits 10 a).sum + (digits 10 b).sum := by
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · simp
  have hlen : (digits 10 a).length ≤ m := (Nat.digits_length_le_iff (by norm_num) a).mpr ha
  have h := Nat.digits_append_zeroes_append_digits (b := 10) (k := m - (digits 10 a).length)
    (m := b) (n := a) (by norm_num) hb
  rw [show (digits 10 a).length + (m - (digits 10 a).length) = m by omega] at h
  rw [← h]
  simp

/-- The digit sum of `x` is at most `9 + x / 10` (last digit plus a crude bound on the rest). -/
theorem digitSum_le (x : ℕ) : (digits 10 x).sum ≤ 9 + x / 10 := by
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · simp
  rw [Nat.digits_def' (by norm_num) hx, List.sum_cons]
  have h1 := Nat.digit_sum_le 10 (x / 10)
  have h2 : x % 10 < 10 := Nat.mod_lt _ (by norm_num)
  omega

/-- Pigeonhole: the powers of 10 modulo `n` repeat. -/
theorem pow_period (n : ℕ) (hn : 0 < n) : ∃ i P, 0 < P ∧ 10 ^ (i + P) % n = 10 ^ i % n := by
  have hc : (Finset.range n).card < (Finset.range (n + 1)).card := by simp
  obtain ⟨x, -, y, -, hxy, h⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to hc
    (f := fun k => 10 ^ k % n) (by intro k _; simpa using Nat.mod_lt _ hn)
  rcases Nat.lt_or_gt_of_ne hxy with h' | h'
  · exact ⟨x, y - x, by omega, by rw [Nat.add_sub_cancel' h'.le]; exact h.symm⟩
  · exact ⟨y, x - y, by omega, by rw [Nat.add_sub_cancel' h'.le]; exact h⟩

/-- A period `P` of the powers of 10 from exponent `i` on may be added `t` times to any
exponent `i + c`. -/
theorem pow_period_mul (n i P : ℕ) (h : 10 ^ (i + P) % n = 10 ^ i % n) (c t : ℕ) :
    10 ^ (i + c + P * t) % n = 10 ^ (i + c) % n := by
  induction t with
  | zero => simp
  | succ t ih =>
    have h1 : 10 ^ (i + c + P * (t + 1)) = 10 ^ (i + P) * 10 ^ (c + P * t) := by
      rw [← pow_add]; congr 1; ring
    have h2 : 10 ^ (i + c + P * t) = 10 ^ i * 10 ^ (c + P * t) := by
      rw [← pow_add]; congr 1; ring
    have h3 : 10 ^ (i + P) * 10 ^ (c + P * t) ≡ 10 ^ i * 10 ^ (c + P * t) [MOD n] :=
      Nat.ModEq.mul_right _ h
    rw [h1]
    exact h3.trans (by rw [← h2]; exact ih)

/-- `k` copies of the list `Y`. -/
def rp (Y : List ℕ) : ℕ → List ℕ
  | 0 => []
  | k + 1 => Y ++ rp Y k

/-- `1 + B + ... + B^(k-1)`. -/
def rep (B : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => 1 + B * rep B k

theorem rp_comm (Y : List ℕ) (k : ℕ) : rp Y k ++ Y = Y ++ rp Y k := by
  induction k with
  | zero => simp [rp]
  | succ k ih => simp only [rp, List.append_assoc, ih]

theorem rp_reverse (Y : List ℕ) (k : ℕ) : (rp Y k).reverse = rp Y.reverse k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [rp, List.reverse_append, ih]
    exact rp_comm Y.reverse k

theorem mem_rp {Y : List ℕ} {k x : ℕ} (h : x ∈ rp Y k) : x ∈ Y := by
  induction k with
  | zero => simp [rp] at h
  | succ k ih =>
    simp only [rp, List.mem_append] at h
    rcases h with h | h
    · exact h
    · exact ih h

/-- Repeating a digit block `k` times multiplies its value by the base-`10^|Y|` repunit. -/
theorem ofDigits_rp (Y : List ℕ) (k : ℕ) :
    Nat.ofDigits 10 (rp Y k) = Nat.ofDigits 10 Y * rep (10 ^ Y.length) k := by
  induction k with
  | zero => simp [rp, rep]
  | succ k ih => rw [rp, Nat.ofDigits_append, ih, rep]; ring

/-- Geometric sum: `(1 + B + ... + B^(k-1)) (B - 1) + 1 = B^k`. -/
theorem rep_mul (B k : ℕ) (hB : 1 ≤ B) : rep B k * (B - 1) + 1 = B ^ k := by
  obtain ⟨c, rfl⟩ : ∃ c, B = c + 1 := ⟨B - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  induction k with
  | zero => simp [rep]
  | succ k ih => rw [rep, pow_succ, ← ih]; ring

/-- If `gcd(m, 10) = 1`, `m` divides a base-`10^L` repunit with at least two ones
(`k = 2 φ(m (10^L - 1))` ones, by Euler's theorem). -/
theorem dvd_rep (m L : ℕ) (hm : 0 < m) (hL : 1 ≤ L) (hc : Nat.Coprime 10 m) :
    ∃ j, m ∣ rep (10 ^ L) (j + 2) := by
  set B := 10 ^ L with hBdef
  have hB : 10 ≤ B := by
    calc 10 = 10 ^ 1 := by norm_num
      _ ≤ 10 ^ L := Nat.pow_le_pow_right (by norm_num) hL
  set M := m * (B - 1)
  have hMpos : 0 < M := Nat.mul_pos hm (by omega)
  have hcop : Nat.Coprime B M := by
    apply Nat.Coprime.mul_right (Nat.Coprime.pow_left L hc)
    exact (Nat.coprime_self_sub_right (by omega)).2 (Nat.coprime_one_right B)
  have ht : 0 < φ M := Nat.totient_pos.2 hMpos
  refine ⟨2 * φ M - 2, ?_⟩
  have hk : 2 * φ M - 2 + 2 = 2 * φ M := by omega
  rw [hk]
  have h1 : B ^ (2 * φ M) ≡ 1 [MOD M] := by
    rw [mul_comm, pow_mul]
    simpa using (Nat.ModEq.pow_totient hcop).pow 2
  have h2 : M ∣ B ^ (2 * φ M) - 1 :=
    (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ (by omega))).1 h1.symm
  have h3 := rep_mul B (2 * φ M) (by omega)
  rw [show B ^ (2 * φ M) - 1 = rep B (2 * φ M) * (B - 1) by omega] at h2
  exact Nat.dvd_of_mul_dvd_mul_right (by omega) h2

end OpenProblemsLib.Digits10
