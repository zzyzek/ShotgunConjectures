/-
OEIS A225003 (dead, "Duplicate of A047332"), Mathlib proof of R. J. Mathar's conjecture
"a(n) = A047332(n), n > 1".

A225003(n) (offset 1, original name): floor(1/f(x^(1/n))) for x = e^(5/7), f = fractional
part  (`A225003`, real power `Real.exp (5/7) ^ (1/n)`).
A047332(n) (offset 1): numbers congruent to {0, 2, 3, 5, 6} mod 7, in increasing order
(`A047332`, as `Nat.nth` of that predicate at n - 1).

Main theorems.
- `A047332_formula`: A047332 n = (7n - 3)/5 (floor) for n ≥ 1.
- `A225003_formula`: A225003 n = (7n - 3)/5 for n ≥ 2.
- `A225003_conjecture`: A225003 n = A047332 n for n ≥ 2.
Argument: with t = 5/(7n) ≤ 5/14, 1 + t + t²/2 ≤ e^t ≤ 1 + t + t²/2 + 2t³/9
(`Real.quadratic_le_exp_of_nonneg`, `Real.exp_bound'`), so frac(e^t) = e^t - 1 and
7n/5 - 3/5 ≤ 1/(e^t - 1) < 7n/5 - 2/5, an interval holding exactly one integer,
floor((7n-3)/5).

Not checked in Lean: the listed terms (certificate/check_A225003.py compares them).
-/
import Mathlib

open Real

/-- A225003(n) = floor(1 / frac((e^(5/7))^(1/n))). -/
noncomputable def A225003 (n : ℕ) : ℤ :=
  ⌊1 / Int.fract (Real.exp (5 / 7) ^ ((1 : ℝ) / n))⌋

/-- The residues of A047332. -/
def A047332_P (m : ℕ) : Prop := m % 7 = 0 ∨ m % 7 = 2 ∨ m % 7 = 3 ∨ m % 7 = 5 ∨ m % 7 = 6

/-- A047332(n): the n-th number (n ≥ 1) congruent to 0, 2, 3, 5 or 6 mod 7. -/
noncomputable def A047332 (n : ℕ) : ℕ := Nat.nth A047332_P (n - 1)

theorem A047332_formula (n : ℕ) (hn : 1 ≤ n) : A047332 n = (7 * n - 3) / 5 := by
  have hinf : (Set.ofPred A047332_P).Infinite := by
    apply Set.infinite_of_forall_exists_gt
    intro a
    exact ⟨7 * (a + 1), by show A047332_P _; unfold A047332_P; omega, by omega⟩
  have hS : ∀ k, k ∈ {n : ℕ | ∀ hf : Set.Finite (Set.ofPred A047332_P), n < hf.toFinset.card} :=
    fun k hf => absurd hf hinf
  have key := Nat.eq_nth_of_strictMonoOn_of_mapsTo_of_surjOn (p := A047332_P)
    (fun k => (7 * k + 4) / 5)
    (fun m hm => ⟨5 * m / 7, hS _, by
      have : A047332_P m := hm
      unfold A047332_P at this
      show (7 * (5 * m / 7) + 4) / 5 = m
      omega⟩)
    (fun k _ => by show A047332_P ((7 * k + 4) / 5); unfold A047332_P; omega)
    (fun a _ b _ hab => by show (7 * a + 4) / 5 < (7 * b + 4) / 5; omega)
    (hS (n - 1))
  unfold A047332
  rw [← key]
  show (7 * (n - 1) + 4) / 5 = (7 * n - 3) / 5
  omega

/-- The analytic step: floor(1/frac(e^(5/(7n)))) = floor((7n-3)/5) for n ≥ 2. -/
theorem A225003_floor_exp (n : ℕ) (hn : 2 ≤ n) :
    ⌊1 / Int.fract (Real.exp (5 / (7 * n)))⌋ = (((7 * n - 3) / 5 : ℕ) : ℤ) := by
  set q : ℕ := (7 * n - 3) / 5 with hqdef
  have hq1 : 5 * q + 3 ≤ 7 * n := by omega
  have hq2 : 7 * n ≤ 5 * q + 7 := by omega
  have hq1r : (5 * q + 3 : ℝ) ≤ 7 * n := by exact_mod_cast hq1
  have hq2r : (7 * n : ℝ) ≤ 5 * q + 7 := by exact_mod_cast hq2
  have hnr : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  set t : ℝ := 5 / (7 * n) with ht
  have hN : (0 : ℝ) < 7 * n := by linarith
  have htN : t * (7 * n) = 5 := by rw [ht]; field_simp
  have ht0 : 0 < t := by positivity
  have ht1 : t ≤ 5 / 14 := by
    rw [ht, div_le_div_iff₀ hN (by norm_num)]
    linarith
  have hlo := Real.quadratic_le_exp_of_nonneg ht0.le
  have hhi := Real.exp_bound' ht0.le (by linarith) (n := 3) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at hhi
  -- hhi : exp t ≤ 1 + t + t^2/2 + t^3 * 4 / 18
  have hhi' : Real.exp t - 1 ≤ t + t ^ 2 / 2 + 2 * t ^ 3 / 9 := by linarith
  have hlo' : t + t ^ 2 / 2 ≤ Real.exp t - 1 := by linarith
  have hd0 : 0 < Real.exp t - 1 := by nlinarith
  have hfl : ⌊Real.exp t⌋ = 1 := by
    rw [Int.floor_eq_iff]
    push_cast
    constructor
    · linarith
    · nlinarith
  rw [Int.fract, hfl]
  push_cast
  rw [Int.floor_eq_iff]
  push_cast
  -- q t ≤ 1 - 3t/5 and (q + 1) t ≥ 1 - 2t/5
  have hqt : (q : ℝ) * t ≤ 1 - 3 / 5 * t := by nlinarith
  have hqt' : 1 - 2 / 5 * t ≤ ((q : ℝ) + 1) * t := by nlinarith
  constructor
  · rw [le_div_iff₀ hd0]
    have h1 : (q : ℝ) * (Real.exp t - 1) ≤ q * (t + t ^ 2 / 2 + 2 * t ^ 3 / 9) :=
      mul_le_mul_of_nonneg_left hhi' hq0
    have h2 : (q : ℝ) * (t + t ^ 2 / 2 + 2 * t ^ 3 / 9)
        = (q * t) * (1 + t / 2 + 2 * t ^ 2 / 9) := by ring
    have h3 : (q * t) * (1 + t / 2 + 2 * t ^ 2 / 9)
        ≤ (1 - 3 / 5 * t) * (1 + t / 2 + 2 * t ^ 2 / 9) :=
      mul_le_mul_of_nonneg_right hqt (by positivity)
    have h4 : (1 - 3 / 5 * t) * (1 + t / 2 + 2 * t ^ 2 / 9) ≤ 1 := by
      nlinarith [sq_nonneg t, pow_pos ht0 3]
    linarith
  · rw [div_lt_iff₀ hd0]
    have h1 : ((q : ℝ) + 1) * (t + t ^ 2 / 2) ≤ ((q : ℝ) + 1) * (Real.exp t - 1) :=
      mul_le_mul_of_nonneg_left hlo' (by linarith)
    have h2 : ((q : ℝ) + 1) * (t + t ^ 2 / 2) = (((q : ℝ) + 1) * t) * (1 + t / 2) := by ring
    have h3 : (1 - 2 / 5 * t) * (1 + t / 2) ≤ (((q : ℝ) + 1) * t) * (1 + t / 2) :=
      mul_le_mul_of_nonneg_right hqt' (by positivity)
    have h4 : 1 < (1 - 2 / 5 * t) * (1 + t / 2) := by
      nlinarith [mul_pos ht0 (show (0 : ℝ) < 1 / 10 - t / 5 by linarith)]
    linarith

theorem A225003_formula (n : ℕ) (hn : 2 ≤ n) :
    A225003 n = (((7 * n - 3) / 5 : ℕ) : ℤ) := by
  unfold A225003
  have hn0 : (n : ℝ) ≠ 0 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  rw [← Real.exp_mul, show (5 / 7 : ℝ) * (1 / n) = 5 / (7 * n) by field_simp]
  exact A225003_floor_exp n hn

/-- Mathar's conjecture: A225003(n) = A047332(n) for n ≥ 2. -/
theorem A225003_conjecture (n : ℕ) (hn : 2 ≤ n) : A225003 n = A047332 n := by
  rw [A225003_formula n hn, A047332_formula n (by omega)]

