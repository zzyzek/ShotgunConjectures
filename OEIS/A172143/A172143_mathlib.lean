/-
OEIS A172143. Original definition (Stephan 2010): (A172126(n) - 1)/3, where A172126 lists
the numbers 2^l * (4^j - 1)/3 (j >= 1, l >= 0) that are 1 mod 3 (A172126 comment).
Old conjecture (Stephan 2010): the sequence is the union over m >= 1 of the chains
S(m, i) = ((3*A172241(m) + 1) * 4^i - 1)/3, A172241(m) = (8^m - (-1)^m - 9)/18.

  * `A172143_orig a`: 3a + 1 = 2^l * (4^j - 1)/3 for some l >= 0, j >= 1.
  * `A172143_conj a`: 3a + 1 = (3*A172241(m) + 1) * 4^i for some m >= 1, i >= 0
    (equivalently a = S(m, i)); A172241 is the entry's closed form, computed in ℤ.
  * `A172143_main`: the two agree for every a, so the conjecture holds.
Key step: with 64^k = 63q + 1, (4^j - 1)/3 is 21q, 84q + 1, 336q + 5 for j = 3k, 3k+1, 3k+2,
and A172241(2k+1) = 28q, A172241(2k+2) = 224q + 3; the residue mod 3 leaves only
(l even, j = 3k+1) and (l odd, j = 3k+2).
Checked: all of the above. Not checked: the reading of A172126 as its comment's form
2^m (4^k - 1)/3 with 3 | (that - 1).
-/
import Mathlib

/-- (4^j - 1)/3. -/
def A172143_R (j : ℕ) : ℕ := (4 ^ j - 1) / 3

/-- OEIS A172241, a(m) = (8^m - (-1)^m - 9)/18. -/
def A172241 (m : ℕ) : ℤ := (8 ^ m - (-1) ^ m - 9) / 18

def A172143_orig (a : ℕ) : Prop := ∃ l j, 1 ≤ j ∧ 3 * a + 1 = 2 ^ l * A172143_R j

def A172143_conj (a : ℕ) : Prop :=
  ∃ m, 1 ≤ m ∧ ∃ i : ℕ, ((3 * a + 1 : ℕ) : ℤ) = (3 * A172241 m + 1) * 4 ^ i

theorem A172143_one_mod (c n : ℕ) : ∃ q, (c + 1) ^ n = c * q + 1 := by
  induction n with
  | zero => exact ⟨0, by simp⟩
  | succ n ih =>
    obtain ⟨q, hq⟩ := ih
    exact ⟨q * (c + 1) + 1, by rw [pow_succ, hq]; ring⟩

theorem A172143_R_spec (j : ℕ) : 3 * A172143_R j + 1 = 4 ^ j := by
  obtain ⟨q, hq⟩ := A172143_one_mod 3 j
  norm_num at hq
  unfold A172143_R
  omega

theorem A172241_odd (k q : ℕ) (hq : 64 ^ k = 63 * q + 1) : A172241 (2 * k + 1) = 28 * q := by
  have hq' : (64 : ℤ) ^ k = 63 * q + 1 := by exact_mod_cast hq
  have h8 : (8 : ℤ) ^ (2 * k + 1) = 8 * 64 ^ k := by rw [pow_succ, pow_mul]; norm_num; ring
  have h1 : (-1 : ℤ) ^ (2 * k + 1) = -1 := by rw [pow_succ, pow_mul]; norm_num
  unfold A172241
  rw [h8, h1, hq']
  omega

theorem A172241_even (k q : ℕ) (hq : 64 ^ k = 63 * q + 1) :
    A172241 (2 * k + 2) = 224 * q + 3 := by
  have hq' : (64 : ℤ) ^ k = 63 * q + 1 := by exact_mod_cast hq
  have h8 : (8 : ℤ) ^ (2 * k + 2) = 64 * 64 ^ k := by
    rw [show 2 * k + 2 = 2 * (k + 1) by ring, pow_mul]; norm_num; ring
  have h1 : (-1 : ℤ) ^ (2 * k + 2) = 1 := by
    rw [show 2 * k + 2 = 2 * (k + 1) by ring, pow_mul]; norm_num
  unfold A172241
  rw [h8, h1, hq']
  omega

theorem A172143_R_cases (k q : ℕ) (hq : 64 ^ k = 63 * q + 1) :
    A172143_R (3 * k) = 21 * q ∧ A172143_R (3 * k + 1) = 84 * q + 1 ∧
      A172143_R (3 * k + 2) = 336 * q + 5 := by
  have e0 := A172143_R_spec (3 * k)
  have e1 := A172143_R_spec (3 * k + 1)
  have e2 := A172143_R_spec (3 * k + 2)
  have p0 : (4 : ℕ) ^ (3 * k) = 64 ^ k := by rw [pow_mul]; norm_num
  have p1 : (4 : ℕ) ^ (3 * k + 1) = 4 * 64 ^ k := by rw [pow_succ, p0]; ring
  have p2 : (4 : ℕ) ^ (3 * k + 2) = 16 * 64 ^ k := by rw [pow_add, p0]; ring
  rw [p0, hq] at e0
  rw [p1, hq] at e1
  rw [p2, hq] at e2
  refine ⟨by omega, by omega, by omega⟩

theorem A172143_main (a : ℕ) : A172143_orig a ↔ A172143_conj a := by
  constructor
  · rintro ⟨l, j, hj, h⟩
    obtain ⟨q, hq⟩ := A172143_one_mod 63 (j / 3)
    obtain ⟨r, hr⟩ := A172143_one_mod 3 (l / 2)
    norm_num at hq hr
    obtain ⟨R0, R1, R2⟩ := A172143_R_cases (j / 3) q hq
    have hl : 2 ^ l = 4 ^ (l / 2) * 2 ^ (l % 2) := by
      conv_lhs => rw [← Nat.div_add_mod l 2, pow_add, pow_mul]
      norm_num
    have hj3 : j = 3 * (j / 3) + j % 3 := (Nat.div_add_mod j 3).symm
    have he : l % 2 < 2 := Nat.mod_lt _ (by norm_num)
    have hs : j % 3 < 3 := Nat.mod_lt _ (by norm_num)
    rw [hl] at h
    rw [hj3] at h
    set i := l / 2
    set k := j / 3
    interval_cases hee : l % 2 <;> interval_cases hss : j % 3 <;>
      simp only [Nat.add_zero, pow_zero, mul_one, pow_one] at h
    · rw [R0] at h
      have : 3 * a + 1 = 3 * (r * (21 * q)) + 21 * q := by rw [h, hr]; ring
      omega
    · rw [R1] at h
      refine ⟨2 * k + 1, by omega, i, ?_⟩
      rw [A172241_odd k q hq, h]
      push_cast
      ring
    · rw [R2] at h
      have : 3 * a + 1 = 3 * (r * (336 * q + 5)) + (336 * q + 5) := by rw [h, hr]; ring
      omega
    · rw [R0] at h
      have : 3 * a + 1 = 3 * (r * (42 * q)) + 42 * q := by rw [h, hr]; ring
      omega
    · rw [R1] at h
      have : 3 * a + 1 = 3 * (r * (168 * q + 2)) + (168 * q + 2) := by rw [h, hr]; ring
      omega
    · rw [R2] at h
      refine ⟨2 * k + 2, by omega, i, ?_⟩
      rw [A172241_even k q hq, h]
      push_cast
      ring
  · rintro ⟨m, hm, i, h⟩
    obtain ⟨k, rfl | rfl⟩ : ∃ k, m = 2 * k + 1 ∨ m = 2 * k + 2 :=
      ⟨(m - 1) / 2, by omega⟩
    · obtain ⟨q, hq⟩ := A172143_one_mod 63 k
      norm_num at hq
      obtain ⟨-, R1, -⟩ := A172143_R_cases k q hq
      rw [A172241_odd k q hq] at h
      refine ⟨2 * i, 3 * k + 1, by omega, ?_⟩
      rw [R1, pow_mul]
      have : ((3 * a + 1 : ℕ) : ℤ) = (((2 ^ 2) ^ i * (84 * q + 1) : ℕ) : ℤ) := by
        rw [h]; push_cast; ring
      exact_mod_cast this
    · obtain ⟨q, hq⟩ := A172143_one_mod 63 k
      norm_num at hq
      obtain ⟨-, -, R2⟩ := A172143_R_cases k q hq
      rw [A172241_even k q hq] at h
      refine ⟨2 * i + 1, 3 * k + 2, by omega, ?_⟩
      rw [R2, pow_succ, pow_mul]
      have : ((3 * a + 1 : ℕ) : ℤ) = (((2 ^ 2) ^ i * 2 * (336 * q + 5) : ℕ) : ℤ) := by
        rw [h]; push_cast; ring
      exact_mod_cast this
