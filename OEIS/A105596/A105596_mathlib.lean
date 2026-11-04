/-
OEIS A105594, A105595, A105596: Mathlib proof that A105596 is 1 mod 4.

Definitions, transcribed from the OEIS formulas.
- `A105594 n k` = (Σ_{j=0..n} |μ(C(n,j))| · (C(j,k) mod 2)) mod 2 (A105594 formula).
- `A105595 n` = Σ_{k=0..n} A105594 n k (row sums, A105595 name).
- `A105596_c b m` = Σ_{k=0..m} (-1)^k b(k) b(m-k), and `A105596 n` = c(2n) for
  b = A105595 (the printed sequence suppresses the zero terms c(2n+1)).

Main theorem `A105596_main`: for every n, c(2n+1) = 0 and A105596 n ≡ 1 (mod 4),
c taken with b = A105595. This is the README result (OEIS conjecture
"a(2n)=1 mod 4, a(2n+1)=0" under the README reading of the indices).

Steps. `A105595_odd`: every A105595 term is odd (B. Gao's argument in
A105595, modulo 2 the row sum is Σ_j |μ(C(n,j))| 2^j ≡ |μ(1)| = 1).
`A105596_of_odd`: the mod-4 statement for any sequence of odd integers.

Not checked: nothing outside Lean; the definitions are hand transcriptions
of the OEIS formulas (certificate/check.py compares them with the OEIS data
in Python).
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

theorem A105596_of_odd (b : ℕ → ℤ) (hb : ∀ k, Odd (b k)) (n : ℕ) :
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

/-- A105594, T(n,k) = (Σ_{j ≤ n} |μ(C(n,j))| · (C(j,k) mod 2)) mod 2. -/
def A105594 (n k : ℕ) : ℕ :=
  (∑ j ∈ Finset.range (n + 1),
    (ArithmeticFunction.moebius (n.choose j)).natAbs * (j.choose k % 2)) % 2

/-- A105595, the row sums of A105594. -/
def A105595 (n : ℕ) : ℕ := ∑ k ∈ Finset.range (n + 1), A105594 n k

/-- A105596, c(2n) for b = A105595. -/
def A105596 (n : ℕ) : ℤ := A105596_c (fun k => (A105595 k : ℤ)) (2 * n)

theorem A105595_sum_choose {j n : ℕ} (hj : j ≤ n) :
    ∑ k ∈ Finset.range (n + 1), j.choose k = 2 ^ j := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hj
  rw [show j + d + 1 = (j + 1) + d by ring, Finset.sum_range_add, Nat.sum_range_choose]
  simp only [add_eq_left]
  exact Finset.sum_eq_zero fun i _ => Nat.choose_eq_zero_of_lt (by omega)

theorem A105595_odd (n : ℕ) : Odd (A105595 n) := by
  rw [← ZMod.natCast_eq_one_iff_odd, A105595]
  simp only [A105594, Nat.cast_sum, ZMod.natCast_mod, Nat.cast_mul]
  rw [Finset.sum_comm]
  have h : ∀ j ∈ Finset.range (n + 1),
      ∑ k ∈ Finset.range (n + 1),
        ((ArithmeticFunction.moebius (n.choose j)).natAbs : ZMod 2) * ((j.choose k : ℕ) : ZMod 2) =
      ((ArithmeticFunction.moebius (n.choose j)).natAbs : ZMod 2) * ((2 ^ j : ℕ) : ZMod 2) := by
    intro j hj
    rw [← Finset.mul_sum, ← Nat.cast_sum,
      A105595_sum_choose (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj))]
  rw [Finset.sum_congr rfl h, Finset.sum_range_succ']
  have h0 : ∀ i ∈ Finset.range n,
      ((ArithmeticFunction.moebius (n.choose (i + 1))).natAbs : ZMod 2) *
        ((2 ^ (i + 1) : ℕ) : ZMod 2) = 0 := by
    intro i _
    rw [pow_succ, Nat.cast_mul, Nat.cast_ofNat]
    simp [show (2 : ZMod 2) = 0 from rfl]
  rw [Finset.sum_eq_zero h0]
  simp

theorem A105596_main (n : ℕ) :
    A105596_c (fun k => (A105595 k : ℤ)) (2 * n + 1) = 0 ∧ A105596 n % 4 = 1 :=
  A105596_of_odd _ (fun k => (A105595_odd k).natCast) n
