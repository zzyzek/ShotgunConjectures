/-
OEIS A105596, Mathlib proof of the reduction to the oddness of A105595.

A105596: c(m) = Σ_{k=0}^{m} (-1)^k b(k) b(m-k) with b = A105595 (the
printed sequence suppresses the zero terms). Conjecture: a(2n) ≡ 1 (mod 4)
and a(2n+1) = 0, indices referring to c (README reading).

Main theorem `A105596_main`: for every b : ℕ → ℤ whose values are all odd,
c(2n+1) = 0 and c(2n) ≡ 1 (mod 4) for all n.

Not checked here: that every term of A105595 is odd (B. Gao, comment in
A105595, Sep 2026); with it, the theorem gives the README result. A105595 is
not defined in this file.
-/
import Mathlib

/-- c(m) = Σ_{k ≤ m} (-1)^k b(k) b(m - k). -/
def A105596_c (b : ℕ → ℤ) (m : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (m + 1), (-1) ^ k * b k * b (m - k)

theorem A105596_neg_one_pow_sub {m k : ℕ} (hk : k ≤ m) :
    ((-1 : ℤ) ^ (m - k)) = (-1) ^ m * (-1) ^ k := by
  have : ((-1 : ℤ) ^ (m - k)) * (-1) ^ k = (-1) ^ m := by
    rw [← pow_add, Nat.sub_add_cancel hk]
  calc ((-1 : ℤ) ^ (m - k)) = ((-1 : ℤ) ^ (m - k)) * ((-1) ^ k * (-1) ^ k) := by
        rw [← pow_add, ← two_mul, pow_mul]; simp
    _ = (-1) ^ m * (-1) ^ k := by rw [← mul_assoc, this]

/-- Reflection k ↦ m - k. -/
theorem A105596_reflect (b : ℕ → ℤ) (m : ℕ) :
    A105596_c b m = (-1) ^ m * A105596_c b m := by
  conv_lhs => rw [A105596_c, ← Finset.sum_range_reflect]
  rw [A105596_c, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k ≤ m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
  rw [Nat.add_sub_cancel, Nat.sub_sub_self hk', A105596_neg_one_pow_sub hk']
  ring

theorem A105596_alt_sum (n : ℕ) : ∑ k ∈ Finset.range (2 * n + 1), (-1 : ℤ) ^ k = 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) + 1 = 2 * n + 1 + 1 + 1 by ring, Finset.sum_range_succ,
      Finset.sum_range_succ, ih]
    rw [pow_succ, pow_succ, show 2 * n + 1 = 2 * n + 1 from rfl, pow_succ, pow_mul]
    simp

theorem A105596_main (b : ℕ → ℤ) (hb : ∀ k, Odd (b k)) (n : ℕ) :
    A105596_c b (2 * n + 1) = 0 ∧ A105596_c b (2 * n) % 4 = 1 := by
  constructor
  · have h := A105596_reflect b (2 * n + 1)
    rw [pow_succ, pow_mul] at h
    simp at h
    linarith
  · choose e he using hb
    set m := 2 * n
    have hS2 : ∑ k ∈ Finset.range (m + 1), (-1 : ℤ) ^ k * e (m - k) =
        ∑ k ∈ Finset.range (m + 1), (-1 : ℤ) ^ k * e k := by
      rw [← Finset.sum_range_reflect]
      refine Finset.sum_congr rfl fun k hk => ?_
      have hk' : k ≤ m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
      rw [Nat.add_sub_cancel, Nat.sub_sub_self hk', A105596_neg_one_pow_sub hk']
      simp [m, pow_mul]
    have hc : A105596_c b m = 1 + 4 * (∑ k ∈ Finset.range (m + 1), (-1 : ℤ) ^ k * e k) +
        4 * (∑ k ∈ Finset.range (m + 1), (-1 : ℤ) ^ k * (e k * e (m - k))) := by
      have hexp : A105596_c b m = ∑ k ∈ Finset.range (m + 1), (-1 : ℤ) ^ k +
          2 * (∑ k ∈ Finset.range (m + 1), (-1 : ℤ) ^ k * e k) +
          2 * (∑ k ∈ Finset.range (m + 1), (-1 : ℤ) ^ k * e (m - k)) +
          4 * (∑ k ∈ Finset.range (m + 1), (-1 : ℤ) ^ k * (e k * e (m - k))) := by
        rw [A105596_c, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
          ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [he k, he (m - k)]
        ring
      rw [hexp, hS2, A105596_alt_sum]
      ring
    rw [hc]
    omega
