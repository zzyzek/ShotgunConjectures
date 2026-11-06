/-
OEIS A165460, A165462, A165463 (Jacobi-bridge heights, Antti Karttunen).

Definitions (as in the OEIS names):
* `S m N = Sum_{i=0..N} J(i, m)` (J = Mathlib's `jacobiSym`);
* A165601(n) = S(4n+3, 2n+1); A165605(n) = A165601(3n+1); A165460(n) = S(12n+7, 4n+2);
* A165602 = positions of zeros of A165601; A165603 = {4n+3 : A165601(n) = 0};
* A165463 = {12n+7 : A165460(n) = 0}; A165462 = {(m-3)/4 : m in A165463} = {3n+1 : A165460(n) = 0}.

Checked here (Lean + Mathlib, no sorry, no native_decide):
* `A165460_conjecture`: A165460(2n) = 2*A165605(2n) and 3*A165460(2n+1) = 2*A165605(2n+1).
* `A165462_conjecture`: k is in A165462 iff k is in A165602 and k = 1 (mod 3).
* `A165463_subset`: every term of A165463 is in A165603.
Route: for the odd character chi = J(., m), T = Sum_{i<m} i chi(i) satisfies
k chi(k) T = T + m chi(k) Sum_{i<m} floor(k i/m) chi(i) (`mult`, reindexing i -> k i mod m);
the floor sums are -A (k = 2) and -2B (k = 3) by the reflection chi(m-i) = -chi(i);
J(2, m) = +-1 by m mod 8 and J(3, m) = -1 by reciprocity (m = 7 mod 12).
Declarations live in namespace JacobiBridge (left open so the axiom check can name them).
Not checked in Lean: agreement with the OEIS data (certificate/check.py).
-/
import Mathlib

open Finset

namespace JacobiBridge

/-- `Sum_{i=0..N} J(i, m)`. -/
def S (m N : ℕ) : ℤ := ∑ i ∈ range (N + 1), jacobiSym (i : ℤ) m

/-- A165601: midpoint height of the Jacobi-bridge for 4n+3. -/
def A165601 (n : ℕ) : ℤ := S (4 * n + 3) (2 * n + 1)

/-- A165605: trisection 3n+1 of A165601. -/
def A165605 (n : ℕ) : ℤ := A165601 (3 * n + 1)

/-- A165460: height at the 1/3 point of the Jacobi-bridge for 12n+7. -/
def A165460 (n : ℕ) : ℤ := S (12 * n + 7) (4 * n + 2)

/-- The character `i ↦ J(i, m)` on naturals. -/
def chi (m i : ℕ) : ℤ := jacobiSym (i : ℤ) m

lemma chi_mod (m i : ℕ) : chi m (i % m) = chi m i := by
  simp only [chi]
  rw [Int.natCast_mod, ← jacobiSym.mod_left]

lemma chi_mul (m a b : ℕ) : chi m (a * b) = chi m a * chi m b := by
  simp only [chi, Nat.cast_mul, jacobiSym.mul_left]

lemma chi_self {m : ℕ} (hm : 1 < m) : chi m m = 0 := by
  rw [← chi_mod, Nat.mod_self]
  simp [chi, jacobiSym.zero_left hm]

lemma chi_refl {m : ℕ} (hm : m % 4 = 3) {i : ℕ} (hi : i ≤ m) : chi m (m - i) = -chi m i := by
  have hodd : Odd m := Nat.odd_iff.mpr (by omega)
  simp only [chi]
  rw [Nat.cast_sub hi]
  have h1 : ((m : ℤ) - i) % m = ((-1) * (i : ℤ)) % m := by
    have : (m : ℤ) - i = (-1) * (i : ℤ) + m * 1 := by ring
    rw [this, Int.add_mul_emod_self_left]
  rw [jacobiSym.mod_left' h1, jacobiSym.mul_left, jacobiSym.at_neg_one hodd,
    ZMod.χ₄_nat_three_mod_four hm]
  ring

/-- Reindexing by `i ↦ k i mod m` for `k` coprime to `m`. -/
lemma sum_perm {m k : ℕ} (hm : 0 < m) (hk : Nat.Coprime k m) (g : ℕ → ℤ) :
    ∑ i ∈ range m, g (k * i % m) = ∑ i ∈ range m, g i := by
  have hinj : Function.Injective (fun i : Fin m => (⟨k * i % m, Nat.mod_lt _ hm⟩ : Fin m)) := by
    intro i j hij
    simp only [Fin.mk.injEq] at hij
    have h2 : (i : ℕ) ≡ j [MOD m] :=
      Nat.ModEq.cancel_left_of_coprime (by rw [Nat.gcd_comm]; exact hk) hij
    exact Fin.ext (Nat.ModEq.eq_of_lt_of_lt h2 i.isLt j.isLt)
  let e := Equiv.ofBijective _ (Finite.injective_iff_bijective.mp hinj)
  rw [← Fin.sum_univ_eq_sum_range (fun i => g (k * i % m)), ← Fin.sum_univ_eq_sum_range g]
  exact e.sum_comp (fun j : Fin m => g j)

lemma mult {m k : ℕ} (hm : 0 < m) (hk : Nat.Coprime k m) :
    (k : ℤ) * chi m k * ∑ i ∈ range m, (i : ℤ) * chi m i =
      ∑ i ∈ range m, (i : ℤ) * chi m i +
        m * chi m k * ∑ i ∈ range m, ((k * i / m : ℕ) : ℤ) * chi m i := by
  have e1 : ∀ i : ℕ, (k : ℤ) * chi m k * ((i : ℤ) * chi m i) =
      ((k * i % m : ℕ) : ℤ) * chi m (k * i % m) +
        m * chi m k * (((k * i / m : ℕ) : ℤ) * chi m i) := by
    intro i
    rw [chi_mod, chi_mul]
    have h := congrArg (Nat.cast (R := ℤ)) (Nat.mod_add_div (k * i) m)
    push_cast at h
    have h' : ((k * i % m : ℕ) : ℤ) = (k : ℤ) * i - m * ((k * i / m : ℕ) : ℤ) := by
      push_cast; linarith
    rw [h']
    ring
  rw [mul_sum, mul_sum, sum_congr rfl (fun i _ => e1 i), sum_add_distrib,
    sum_perm hm hk (fun j => (j : ℤ) * chi m j)]

/-! ### Sums of chi over pieces of [0, m] -/

section pieces

variable {m : ℕ} (hm : m % 4 = 3)
include hm

lemma one_lt : 1 < m := by omega

lemma range_succ_eq (f : ℕ → ℤ) :
    ∑ i ∈ range m, f i * chi m i = ∑ i ∈ range (m + 1), f i * chi m i := by
  rw [sum_range_succ, chi_self (one_lt hm), mul_zero, add_zero]

lemma reflect (P : ℕ → Prop) [DecidablePred P] :
    ∑ i ∈ range (m + 1), (if P i then chi m i else 0) =
      -∑ i ∈ range (m + 1), (if P (m - i) then chi m i else 0) := by
  rw [← sum_range_reflect, ← sum_neg_distrib]
  refine sum_congr rfl fun i hi => ?_
  have hi' : i ≤ m := by simp at hi; omega
  simp only [Nat.add_sub_cancel]
  split_ifs with h1
  · rw [chi_refl hm hi']
  · simp

lemma sum_le (N : ℕ) (hN : N ≤ m) :
    ∑ i ∈ range (m + 1), (if i ≤ N then chi m i else 0) = ∑ i ∈ range (N + 1), chi m i := by
  rw [← sum_filter]
  congr 1
  ext i
  simp only [mem_filter, mem_range]
  omega

lemma sum_all : ∑ i ∈ range (m + 1), chi m i = 0 := by
  have h := reflect hm (fun _ => True)
  simp only [ite_true] at h
  linarith

lemma D2 : ∑ i ∈ range m, ((2 * i / m : ℕ) : ℤ) * chi m i = -S m ((m - 1) / 2) := by
  have hq : ∀ i ∈ range (m + 1), ((2 * i / m : ℕ) : ℤ) * chi m i =
      if m - i ≤ (m - 1) / 2 then chi m i else 0 := by
    intro i hi
    simp only [mem_range] at hi
    by_cases him : i = m
    · subst him; simp [chi_self (one_lt hm)]
    have hm0 : 0 < m := by omega
    split_ifs with h
    · have u1 := (Nat.div_lt_iff_lt_mul hm0).mpr (show 2 * i < 2 * m by omega)
      have u2 := (Nat.le_div_iff_mul_le hm0).mpr (show 1 * m ≤ 2 * i by omega)
      have e : 2 * i / m = 1 := by omega
      rw [e]; simp
    · have e : 2 * i / m = 0 := Nat.div_eq_of_lt (by omega)
      rw [e]; simp
  rw [range_succ_eq hm, sum_congr rfl hq, reflect hm]
  rw [show ∑ i ∈ range (m + 1), (if m - (m - i) ≤ (m - 1) / 2 then chi m i else 0) =
      ∑ i ∈ range (m + 1), (if i ≤ (m - 1) / 2 then chi m i else 0) from
    sum_congr rfl fun i hi => by simp at hi; rw [Nat.sub_sub_self (by omega)]]
  rw [sum_le hm _ (by omega), S]
  rfl

lemma D3 (h3 : m % 3 = 1) :
    ∑ i ∈ range m, ((3 * i / m : ℕ) : ℤ) * chi m i = -2 * S m ((m - 1) / 3) := by
  have hq : ∀ i ∈ range (m + 1), ((3 * i / m : ℕ) : ℤ) * chi m i =
      chi m i - (if i ≤ (m - 1) / 3 then chi m i else 0) +
        (if m - i ≤ (m - 1) / 3 then chi m i else 0) := by
    intro i hi
    simp only [mem_range] at hi
    by_cases him : i = m
    · subst him; simp [chi_self (one_lt hm)]
    have hm0 : 0 < m := by omega
    have u3 := (Nat.div_lt_iff_lt_mul hm0).mpr (show 3 * i < 3 * m by omega)
    split_ifs with g1 g2 g2
    · omega
    · have e : 3 * i / m = 0 := Nat.div_eq_of_lt (by omega)
      rw [e]; simp
    · have u2 := (Nat.le_div_iff_mul_le hm0).mpr (show 2 * m ≤ 3 * i by omega)
      have e : 3 * i / m = 2 := by omega
      rw [e]; push_cast; ring
    · have u1 := (Nat.le_div_iff_mul_le hm0).mpr (show 1 * m ≤ 3 * i by omega)
      have u2 := (Nat.div_lt_iff_lt_mul hm0).mpr (show 3 * i < 2 * m by omega)
      have e : 3 * i / m = 1 := by omega
      rw [e]; simp
  rw [range_succ_eq hm, sum_congr rfl hq, sum_add_distrib, sum_sub_distrib, sum_all hm,
    sum_le hm _ (by omega), reflect hm (fun i => m - i ≤ (m - 1) / 3)]
  rw [show ∑ i ∈ range (m + 1), (if m - (m - i) ≤ (m - 1) / 3 then chi m i else 0) =
      ∑ i ∈ range (m + 1), (if i ≤ (m - 1) / 3 then chi m i else 0) from
    sum_congr rfl fun i hi => by simp at hi; rw [Nat.sub_sub_self (by omega)]]
  rw [sum_le hm _ (by omega), S]
  simp only [chi]
  ring

end pieces

lemma chi_two {m : ℕ} (hm : m % 2 = 1) :
    chi m 2 = if m % 8 = 1 ∨ m % 8 = 7 then 1 else -1 := by
  have hodd : Odd m := Nat.odd_iff.mpr hm
  simp only [chi, Nat.cast_ofNat]
  rw [jacobiSym.at_two hodd, ZMod.χ₈_nat_eq_if_mod_eight]
  have hx : ¬(m % 2 = 0) := by omega
  simp only [hx, ite_false]

lemma chi_three {m : ℕ} (hm : m % 12 = 7) : chi m 3 = -1 := by
  simp only [chi, Nat.cast_ofNat]
  have h := jacobiSym.quadratic_reciprocity_three_mod_four (a := 3) (b := m) (by norm_num)
    (by omega)
  push_cast at h
  rw [h, jacobiSym.mod_left]
  have : (m : ℤ) % ((3 : ℕ) : ℤ) = 1 := by push_cast; omega
  rw [this, jacobiSym.one_left]

/-- Key relation between the 1/3-point and the midpoint heights for m = 7 (mod 12). -/
lemma key {m : ℕ} (hm : m % 12 = 7) :
    (m % 8 = 7 → S m ((m - 1) / 3) = 2 * S m ((m - 1) / 2)) ∧
      (m % 8 = 3 → 3 * S m ((m - 1) / 3) = 2 * S m ((m - 1) / 2)) := by
  have hm4 : m % 4 = 3 := by omega
  have hm0 : 0 < m := by omega
  have c2 : Nat.Coprime 2 m := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr (by omega)
  have c3 : Nat.Coprime 3 m := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr (by omega)
  have hT2 := mult hm0 c2
  have hT3 := mult hm0 c3
  rw [D2 hm4] at hT2
  rw [D3 hm4 (by omega), chi_three hm] at hT3
  push_cast at hT2 hT3
  have hmz : (2 * m : ℤ) ≠ 0 := by positivity
  constructor
  · intro h8
    rw [chi_two (by omega)] at hT2
    have hx : m % 8 = 1 ∨ m % 8 = 7 := by omega
    simp only [hx, ite_true] at hT2
    have h : (2 * m : ℤ) * (S m ((m - 1) / 3) - 2 * S m ((m - 1) / 2)) = 0 := by
      linear_combination (-4) * hT2 - hT3
    rcases mul_eq_zero.mp h with h | h
    · exact absurd h hmz
    · linarith
  · intro h8
    rw [chi_two (by omega)] at hT2
    have hx : ¬(m % 8 = 1 ∨ m % 8 = 7) := by omega
    simp only [hx, ite_false] at hT2
    have h : (2 * m : ℤ) * (3 * S m ((m - 1) / 3) - 2 * S m ((m - 1) / 2)) = 0 := by
      linear_combination 4 * hT2 - 3 * hT3
    rcases mul_eq_zero.mp h with h | h
    · exact absurd h hmz
    · linarith

/-- The A165460 conjecture: a(2n) = 2*A165605(2n) and a(2n+1) = (2/3)*A165605(2n+1). -/
theorem A165460_conjecture (n : ℕ) :
    A165460 (2 * n) = 2 * A165605 (2 * n) ∧ 3 * A165460 (2 * n + 1) = 2 * A165605 (2 * n + 1) := by
  simp only [A165460, A165605, A165601]
  constructor
  · have k := (key (m := 12 * (2 * n) + 7) (by omega)).1 (by omega)
    rw [show (12 * (2 * n) + 7 - 1) / 3 = 4 * (2 * n) + 2 by omega,
      show (12 * (2 * n) + 7 - 1) / 2 = 6 * (2 * n) + 3 by omega] at k
    rw [show 4 * (3 * (2 * n) + 1) + 3 = 12 * (2 * n) + 7 by ring,
      show 2 * (3 * (2 * n) + 1) + 1 = 6 * (2 * n) + 3 by ring]
    exact k
  · have k := (key (m := 12 * (2 * n + 1) + 7) (by omega)).2 (by omega)
    rw [show (12 * (2 * n + 1) + 7 - 1) / 3 = 4 * (2 * n + 1) + 2 by omega,
      show (12 * (2 * n + 1) + 7 - 1) / 2 = 6 * (2 * n + 1) + 3 by omega] at k
    rw [show 4 * (3 * (2 * n + 1) + 1) + 3 = 12 * (2 * n + 1) + 7 by ring,
      show 2 * (3 * (2 * n + 1) + 1) + 1 = 6 * (2 * n + 1) + 3 by ring]
    exact k

lemma zero_iff (n : ℕ) : A165460 n = 0 ↔ A165605 n = 0 := by
  rcases Nat.even_or_odd' n with ⟨t, rfl | rfl⟩
  · have := (A165460_conjecture t).1
    constructor <;> intro h <;> linarith
  · have := (A165460_conjecture t).2
    constructor <;> intro h <;> linarith

/-- A165462 (= {3n+1 : A165460(n) = 0}, i.e. (A165463 - 3)/4) is exactly the set of terms of
A165602 (zeros of A165601) that are 1 mod 3. -/
theorem A165462_conjecture (k : ℕ) :
    (∃ n, k = 3 * n + 1 ∧ A165460 n = 0) ↔ (A165601 k = 0 ∧ k % 3 = 1) := by
  constructor
  · rintro ⟨n, rfl, h⟩
    exact ⟨(zero_iff n).mp h, by omega⟩
  · rintro ⟨h, hk⟩
    refine ⟨k / 3, by omega, (zero_iff _).mpr ?_⟩
    rw [A165605, show 3 * (k / 3) + 1 = k by omega]
    exact h

/-- A165463 (numbers 12n+7 with A165460(n) = 0) is a subset of A165603
(numbers 4n+3 with A165601(n) = 0). -/
theorem A165463_subset (m : ℕ) (h : ∃ n, m = 12 * n + 7 ∧ A165460 n = 0) :
    ∃ n, m = 4 * n + 3 ∧ A165601 n = 0 := by
  obtain ⟨n, rfl, h⟩ := h
  exact ⟨3 * n + 1, by ring, (zero_iff n).mp h⟩
