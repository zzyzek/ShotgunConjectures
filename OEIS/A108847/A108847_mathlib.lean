/-
OEIS A108847 (palindromic primes with all internal digits 8), old comment by Cino Hilliard,
moved to A068689 on 2023-01-28: "Inner digits 1 and 2 are the only repeating digits for which
s(x) is prime for outer digits 9. I.e. 9444..4449, 9555..5559, 9777..7779 are composite."
A068689 (primes 9 d...d 9) keeps the corrected form "1, 2 and 8 are the only inner digits".

`A108847_N d k` is the number whose decimal digits are 9, then k copies of d, then 9
(`Nat.ofDigits 10`, least significant digit first; the string is a palindrome).

  * `A108847_digits`: for d ≤ 9 the decimal digits of `A108847_N d k` are exactly that string.
  * `A108847_main`: if d ≤ 9 and `A108847_N d k` is prime then d ∈ {1, 2, 8}.
    Key step: for d ∉ {1, 2, 8} one of 3, 7, 11, 13 divides the number; the residue mod 3003
    has period 6 in k because 3003 divides 10^6 - 1 and 111111.
  * `A108847_witness`: 919, 929 and 9888889 are prime (d = 1, 2, 8).
  * `A108847_comment_false`: the A108847 wording (only 1 and 2) is false, d = 8 gives 9888889.
Checked: everything above. Not checked: nothing beyond reading the OEIS wording.
-/
import Mathlib

/-- The number 9 d...d 9 with k inner digits d. -/
def A108847_N (d k : ℕ) : ℕ := Nat.ofDigits 10 (9 :: List.replicate k d ++ [9])

/-- The repdigit d...d with k digits, built at the low end. -/
def A108847_R (d : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => d + 10 * A108847_R d k

theorem A108847_digits (d k : ℕ) (hd : d ≤ 9) :
    Nat.digits 10 (A108847_N d k) = 9 :: List.replicate k d ++ [9] := by
  unfold A108847_N
  apply Nat.digits_ofDigits _ (by norm_num)
  · intro x hx
    have : x = 9 ∨ x = d := by
      simp at hx
      tauto
    omega
  · intro _
    simp

theorem A108847_R_eq (d k : ℕ) : Nat.ofDigits 10 (List.replicate k d) = A108847_R d k := by
  induction k with
  | zero => simp [A108847_R]
  | succ k ih => simp [List.replicate_succ, Nat.ofDigits_cons, ih, A108847_R]

theorem A108847_N_eq (d k : ℕ) :
    A108847_N d k = 9 + 10 * (A108847_R d k + 10 ^ k * 9) := by
  unfold A108847_N
  rw [List.cons_append, Nat.ofDigits_cons, Nat.ofDigits_append, A108847_R_eq]
  simp

theorem A108847_R_add6 (d k : ℕ) :
    A108847_R d (k + 6) = 111111 * d + 1000000 * A108847_R d k := by
  simp only [A108847_R]
  ring

theorem A108847_period (d k : ℕ) : A108847_N d (k + 6) % 3003 = A108847_N d k % 3003 := by
  rw [A108847_N_eq, A108847_N_eq, A108847_R_add6, pow_add]
  norm_num
  omega

theorem A108847_mod (d k : ℕ) : A108847_N d k % 3003 = A108847_N d (k % 6) % 3003 := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases Nat.lt_or_ge k 6 with h | h
    · rw [Nat.mod_eq_of_lt h]
    · obtain ⟨j, rfl⟩ : ∃ j, k = j + 6 := ⟨k - 6, by omega⟩
      rw [A108847_period, ih j (by omega)]
      congr 2
      omega

theorem A108847_cover :
    ∀ d ∈ [0, 3, 4, 5, 6, 7, 9], ∀ r ∈ [0, 1, 2, 3, 4, 5], ∃ p ∈ [3, 7, 11, 13],
      (A108847_N d r % 3003) % p = 0 := by
  decide

theorem A108847_ge (d k : ℕ) : 99 ≤ A108847_N d k := by
  rw [A108847_N_eq]
  have : 1 ≤ 10 ^ k := Nat.one_le_pow _ _ (by norm_num)
  omega

theorem A108847_main (d k : ℕ) (hd : d ≤ 9) (hp : (A108847_N d k).Prime) :
    d = 1 ∨ d = 2 ∨ d = 8 := by
  by_contra hne
  have hd' : d ∈ [0, 3, 4, 5, 6, 7, 9] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    omega
  have hr : k % 6 ∈ [0, 1, 2, 3, 4, 5] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    omega
  obtain ⟨p, hpm, hpd⟩ := A108847_cover d hd' (k % 6) hr
  rw [← A108847_mod] at hpd
  have h3003 : p ∣ 3003 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hpm
    rcases hpm with rfl | rfl | rfl | rfl <;> norm_num
  rw [Nat.mod_mod_of_dvd _ h3003] at hpd
  have hdvd : p ∣ A108847_N d k := Nat.dvd_of_mod_eq_zero hpd
  have hle : p ≤ 13 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hpm
    omega
  have h1 : p ≠ 1 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hpm
    omega
  rcases hp.eq_one_or_self_of_dvd p hdvd with h | h
  · exact h1 h
  · have := A108847_ge d k
    omega

theorem A108847_witness :
    (A108847_N 1 1).Prime ∧ (A108847_N 2 1).Prime ∧ (A108847_N 8 5).Prime := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num [A108847_N, Nat.ofDigits]

theorem A108847_comment_false : ¬ ∀ d k, d ≤ 9 → (A108847_N d k).Prime → d = 1 ∨ d = 2 := by
  intro h
  have := h 8 5 (by norm_num) A108847_witness.2.2
  omega
