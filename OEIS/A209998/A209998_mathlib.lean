/-
OEIS A209998: triangle of coefficients of v(n,x), where (Mathematica program of the entry, which
reproduces the data) u(1,x) = v(1,x) = 1 and
  u(n,x) = x*u(n-1,x) + 2x*v(n-1,x) + 1,
  v(n,x) = (x+1)*u(n-1,x) + 2x*v(n-1,x) + 1.
Row n lists the coefficients of v(n,x) (degree n-1).
Conjecture (Clark Kimberling): penultimate term in row n is A199923(n), where
A199923(n) = Sum_{k=0..3^(n-1)} gcd(k, 3^(n-1)).

Checked here (Lean + Mathlib, no sorry, no native_decide):
* `A209998_corrected`: for n >= 2, v(n,x) has degree n-1 and its x^(n-2) coefficient
  (the penultimate term of row n) equals A199923(n-1).
* `A209998_literal_false`: the penultimate term of row 2 is 2, while A199923(2) = 8.
* `A199923_formula`: A199923(n) = 2(n+2)3^(n-2) (as 9*A199923(n) = 2(n+2)3^n), n >= 1.
Indexing: `u k`, `v k` here are u(k+1,x), v(k+1,x).
Declarations live in namespace A209998 (left open so the axiom check can name them).
-/
import Mathlib

open Polynomial Finset

namespace A209998

/-- The pair (u(k+1,x), v(k+1,x)). -/
noncomputable def uv : ℕ → ℤ[X] × ℤ[X]
  | 0 => (1, 1)
  | k + 1 => (X * (uv k).1 + X * (C 2 * (uv k).2) + 1,
              (X + 1) * (uv k).1 + X * (C 2 * (uv k).2) + 1)

noncomputable def u (k : ℕ) : ℤ[X] := (uv k).1
noncomputable def v (k : ℕ) : ℤ[X] := (uv k).2

lemma u_succ (k : ℕ) : u (k + 1) = X * u k + X * (C 2 * v k) + 1 := rfl
lemma v_succ (k : ℕ) : v (k + 1) = (X + 1) * u k + X * (C 2 * v k) + 1 := rfl

lemma cu (k i : ℕ) : (u (k + 1)).coeff (i + 1) = (u k).coeff i + 2 * (v k).coeff i := by
  rw [u_succ]
  simp only [coeff_add, coeff_X_mul, coeff_C_mul, coeff_one]
  simp

lemma cv (k i : ℕ) :
    (v (k + 1)).coeff (i + 1) = (u k).coeff i + (u k).coeff (i + 1) + 2 * (v k).coeff i := by
  rw [v_succ, add_mul, one_mul]
  simp only [coeff_add, coeff_X_mul, coeff_C_mul, coeff_one]
  simp

lemma cu0 (k : ℕ) : (u (k + 1)).coeff 0 = 1 := by
  rw [u_succ]
  simp [coeff_add, coeff_one]

lemma cv0 (k : ℕ) : (v (k + 1)).coeff 0 = (u k).coeff 0 + 1 := by
  rw [v_succ, add_mul, one_mul]
  simp [coeff_add, coeff_one]

lemma vanish (k : ℕ) : ∀ i, k < i → (u k).coeff i = 0 ∧ (v k).coeff i = 0 := by
  induction k with
  | zero =>
    intro i hi
    simp [u, v, uv, coeff_one, show i ≠ 0 by omega]
  | succ k ih =>
    intro i hi
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    rw [cu, cv, (ih j (by omega)).1, (ih j (by omega)).2, (ih (j + 1) (by omega)).1]
    simp

lemma top (k : ℕ) : (u k).coeff k = 3 ^ k ∧ (v k).coeff k = 3 ^ k := by
  induction k with
  | zero => simp [u, v, uv]
  | succ k ih =>
    rw [cu, cv, ih.1, ih.2, (vanish k (k + 1) (by omega)).1]
    constructor <;> ring

lemma second (j : ℕ) :
    3 * (u (j + 1)).coeff j = (2 * j + 3) * 3 ^ j ∧
      3 * (v (j + 1)).coeff j = 2 * (j + 3) * 3 ^ j := by
  induction j with
  | zero =>
    rw [cu0, cv0]
    simp [u, uv]
  | succ j ih =>
    rw [cu, cv, (top (j + 1)).1]
    push_cast
    constructor
    · linear_combination ih.1 + 2 * ih.2
    · linear_combination ih.1 + 2 * ih.2

lemma natDegree_v (k : ℕ) : (v k).natDegree = k := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · exact natDegree_le_iff_coeff_eq_zero.mpr fun N hN => (vanish k N hN).2
  · rw [(top k).2]; positivity

/-! ### A199923 -/

/-- OEIS A199923: a(n) = Sum_{k=0..3^(n-1)} gcd(k, 3^(n-1)) for n > 0, a(0) = 1. -/
def A199923 (n : ℕ) : ℕ :=
  if n = 0 then 1 else ∑ k ∈ range (3 ^ (n - 1) + 1), Nat.gcd k (3 ^ (n - 1))

lemma sum_range_three_mul (f : ℕ → ℕ) (N : ℕ) :
    ∑ k ∈ range (3 * N), f k = ∑ j ∈ range N, (f (3 * j) + f (3 * j + 1) + f (3 * j + 2)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [show 3 * (N + 1) = 3 * N + 2 + 1 by ring, sum_range_succ, sum_range_succ, sum_range_succ,
      show 3 * N + 2 = 3 * N + 1 + 1 by ring, ih, sum_range_succ]
    ring

lemma gcd_not_three {k m : ℕ} (hk : ¬ 3 ∣ k) : Nat.gcd k (3 ^ m) = 1 :=
  Nat.Coprime.pow_right m ((Nat.coprime_comm).mp ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hk))

/-- `G m = Sum_{k < 3^m} gcd(k, 3^m)`. -/
lemma G_rec (m : ℕ) : ∑ k ∈ range (3 ^ (m + 1)), Nat.gcd k (3 ^ (m + 1)) =
    2 * 3 ^ m + 3 * ∑ k ∈ range (3 ^ m), Nat.gcd k (3 ^ m) := by
  have key : ∀ j, Nat.gcd (3 * j) (3 ^ (m + 1)) + Nat.gcd (3 * j + 1) (3 ^ (m + 1)) +
      Nat.gcd (3 * j + 2) (3 ^ (m + 1)) = 2 + 3 * Nat.gcd j (3 ^ m) := by
    intro j
    rw [gcd_not_three (k := 3 * j + 1) (m := m + 1) (by omega),
      gcd_not_three (k := 3 * j + 2) (m := m + 1) (by omega), pow_succ', Nat.gcd_mul_left]
    ring
  rw [show 3 ^ (m + 1) = 3 * 3 ^ m from pow_succ' 3 m, sum_range_three_mul]
  rw [← pow_succ', sum_congr rfl (fun j _ => key j), sum_add_distrib, sum_const, card_range,
    smul_eq_mul, mul_sum]
  ring

lemma G_eq (m : ℕ) : 3 * ∑ k ∈ range (3 ^ m), Nat.gcd k (3 ^ m) = (2 * m + 3) * 3 ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [G_rec, pow_succ]
    nlinarith [ih]

/-- Irvine's formula, in the form 9 * A199923(n) = 2 (n+2) 3^n for n >= 1. -/
theorem A199923_formula (n : ℕ) (hn : 1 ≤ n) : 9 * A199923 n = 2 * (n + 2) * 3 ^ n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp only [A199923, Nat.add_one_ne_zero, ite_false, Nat.add_sub_cancel]
  rw [sum_range_succ, Nat.gcd_self, mul_add, show 9 = 3 * 3 by rfl, mul_assoc, G_eq, pow_succ]
  ring

/-- Corrected conjecture: for n >= 2, the penultimate entry of row n (the x^(n-2) coefficient of
v(n,x), which has degree n-1) equals A199923(n-1). Stated with n = j + 2. -/
theorem A209998_corrected (j : ℕ) :
    (v (j + 1)).natDegree = j + 1 ∧ (v (j + 1)).coeff j = (A199923 (j + 1) : ℤ) := by
  refine ⟨natDegree_v _, ?_⟩
  have h1 := (second j).2
  have h2 := A199923_formula (j + 1) (by omega)
  have h3 : (9 : ℤ) * (A199923 (j + 1) : ℤ) = 2 * ((j : ℤ) + 3) * 3 ^ (j + 1) := by
    exact_mod_cast (by rw [h2] : 9 * A199923 (j + 1) = 2 * (j + 3) * 3 ^ (j + 1))
  have : (9 : ℤ) * (v (j + 1)).coeff j = 9 * (A199923 (j + 1) : ℤ) := by
    rw [h3, pow_succ]; linear_combination 3 * h1
  linarith

/-- The literal conjecture fails at row 2: penultimate term 2, A199923(2) = 8. -/
theorem A209998_literal_false : ¬ ∀ n ≥ 2, (v (n - 1)).coeff (n - 2) = (A199923 n : ℤ) := by
  intro h
  have h2 := h 2 le_rfl
  have hv : (v 1).coeff 0 = 2 := by rw [cv0]; simp [u, uv]
  have ha : A199923 2 = 8 := by decide
  simp only [Nat.reduceSub] at h2
  rw [hv, ha] at h2
  norm_num at h2
