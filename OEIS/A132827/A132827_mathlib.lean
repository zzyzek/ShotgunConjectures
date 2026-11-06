/-
OEIS A132827: array read by antidiagonals, data
1, 3, 2, 8, 6, 4, 21, 16, 11, 5, 55, 42, 29, 14, 7, ... (36 terms), with
FORMULA A(i,j) = (b(i)+1) F(2j) + (i - b(i)) F(2j+1), b = A005206.
Conjecture (C. Kimberling, 2011): the array is the dispersion of
f(n) = floor(n*x + n + 1), x the golden ratio.

Definitions.
* `f n = ⌊n φ + n + 1⌋₊`.
* `P m`: m ≥ 1 and m is not f n for any n ≥ 1 (the complement of the range).
* `disp i j = f^[j] (Nat.nth P i)`: row i (from 0) of the dispersion starts at
  the i-th element of the complement and applies f; column j from 0
  (the entry's column j+1).
* `b i = 2 i - ⌊i φ⌋₊`, `X i j = (b i + 1) F(2j+2) + (i - b i) F(2j+3)`.
* `hofG`: A005206 by its definition G(0) = 0, G(n) = n - G(G(n-1)).
* `entryFormula i j`: the entry's FORMULA with b = A005206.

Main theorems.
* `A132827_dispersion`: disp i j = X i j for all i, j (the closed form).
* `nth_P`: the first column is Nat.nth P i = ⌊i φ⌋₊ + 1 (Beatty partition of
  ⌊nφ⌋, ⌊nφ²⌋, Mathlib `Irrational.beattySeq_symmDiff_beattySeq_pos`).
* `A132827_data`: the 36 data terms of the entry are the dispersion read by
  antidiagonals.
* `entryFormula_wrong`: the entry's FORMULA gives 6 at (4,1) (row 4, entry
  column 1) where the data and the dispersion have 7.

Not checked in this file: that the 36 listed terms are the entry's data
(copied by hand from the entry, revision of 2026-11-06).
-/
import Mathlib

open Real
open scoped goldenRatio symmDiff

namespace A132827

/-- Kimberling's f(n) = floor(n*x + n + 1), x = golden ratio. -/
noncomputable def f (n : ℕ) : ℕ := ⌊(n : ℝ) * φ + n + 1⌋₊

/-- m ≥ 1 is not in the range of f on n ≥ 1. -/
def P (m : ℕ) : Prop := 1 ≤ m ∧ ¬ ∃ n, 1 ≤ n ∧ f n = m

/-- The dispersion of f: row i is t(i), f(t(i)), f(f(t(i))), … with t = Nat.nth P. -/
noncomputable def disp (i j : ℕ) : ℕ := f^[j] (Nat.nth P i)

noncomputable def b (i : ℕ) : ℕ := 2 * i - ⌊(i : ℝ) * φ⌋₊

noncomputable def X (i j : ℕ) : ℕ :=
  (b i + 1) * Nat.fib (2 * j + 2) + (i - b i) * Nat.fib (2 * j + 3)

lemma f_eq (n : ℕ) : f n = ⌊(n : ℝ) * φ⌋₊ + n + 1 := by
  have h0 : (0 : ℝ) ≤ n * φ := mul_nonneg (Nat.cast_nonneg _) goldenRatio_pos.le
  unfold f
  rw [Nat.floor_add_one (by positivity), Nat.floor_add_natCast h0]

lemma f_eq_sq (n : ℕ) : f n = ⌊(n : ℝ) * φ ^ 2⌋₊ + 1 := by
  have h0 : (0 : ℝ) ≤ n * φ := mul_nonneg (Nat.cast_nonneg _) goldenRatio_pos.le
  rw [f_eq, goldenRatio_sq, mul_add, mul_one, Nat.floor_add_natCast h0]

lemma fl_bounds (i : ℕ) : i ≤ ⌊(i : ℝ) * φ⌋₊ ∧ ⌊(i : ℝ) * φ⌋₊ ≤ 2 * i := by
  have h1 := one_lt_goldenRatio
  have h2 := goldenRatio_lt_two
  have hi : (0 : ℝ) ≤ i := Nat.cast_nonneg _
  constructor
  · apply Nat.le_floor
    nlinarith
  · have := Nat.floor_le (mul_nonneg hi goldenRatio_pos.le)
    have : (⌊(i : ℝ) * φ⌋₊ : ℝ) ≤ 2 * i := by nlinarith
    exact_mod_cast this

/-! ### Beatty partition in ℕ form -/

lemma holder : Real.HolderConjugate φ (φ ^ 2) := by
  rw [Real.holderConjugate_iff_eq_conjExponent one_lt_goldenRatio]
  have h : φ - 1 ≠ 0 := by have := one_lt_goldenRatio; linarith
  rw [eq_div_iff h]
  linear_combination φ * goldenRatio_sq

lemma beatty_nat (r : ℝ) (hr : 0 ≤ r) (k : ℕ) : beattySeq r k = (⌊(k : ℝ) * r⌋₊ : ℤ) := by
  rw [beattySeq, Int.natCast_floor_eq_floor (mul_nonneg (Nat.cast_nonneg _) hr)]
  push_cast; rfl

lemma beatty_H :
    {beattySeq φ k | k > 0} ∆ {beattySeq (φ ^ 2) k | k > 0} = {n | 0 < n} :=
  Irrational.beattySeq_symmDiff_beattySeq_pos holder goldenRatio_irrational

lemma mem_beatty_iff (r : ℝ) (hr : 0 ≤ r) (m : ℕ) :
    (m : ℤ) ∈ {beattySeq r k | k > 0} ↔ ∃ k : ℕ, 1 ≤ k ∧ ⌊(k : ℝ) * r⌋₊ = m := by
  constructor
  · rintro ⟨k, hk, hkm⟩
    refine ⟨k.toNat, by omega, ?_⟩
    have : ((k.toNat : ℕ) : ℤ) = k := Int.toNat_of_nonneg hk.le
    rw [← this, beatty_nat r hr] at hkm
    exact_mod_cast hkm
  · rintro ⟨k, hk, hkm⟩
    exact ⟨k, by omega, by rw [beatty_nat r hr, hkm]⟩

lemma beatty_disj (i n : ℕ) (hi : 1 ≤ i) (hn : 1 ≤ n) :
    ⌊(i : ℝ) * φ⌋₊ ≠ ⌊(n : ℝ) * φ ^ 2⌋₊ := by
  intro h
  have hpos : 0 < ⌊(i : ℝ) * φ⌋₊ := by have := (fl_bounds i).1; omega
  have hm : ((⌊(i : ℝ) * φ⌋₊ : ℕ) : ℤ) ∈ ({n | 0 < n} : Set ℤ) := by
    show (0 : ℤ) < _; exact_mod_cast hpos
  rw [← beatty_H, Set.mem_symmDiff] at hm
  have h1 := (mem_beatty_iff φ goldenRatio_pos.le _).2 ⟨i, hi, rfl⟩
  have h2 := (mem_beatty_iff (φ ^ 2) (by positivity) _).2 ⟨n, hn, h.symm⟩
  rcases hm with ⟨_, h⟩ | ⟨_, h⟩
  · exact h h2
  · exact h h1

lemma beatty_cover (m : ℕ) (hm : 1 ≤ m) :
    (∃ k : ℕ, 1 ≤ k ∧ ⌊(k : ℝ) * φ⌋₊ = m) ∨ (∃ k : ℕ, 1 ≤ k ∧ ⌊(k : ℝ) * φ ^ 2⌋₊ = m) := by
  have h : (m : ℤ) ∈ ({n | 0 < n} : Set ℤ) := by show (0 : ℤ) < _; exact_mod_cast hm
  rw [← beatty_H, Set.mem_symmDiff] at h
  rcases h with ⟨h, _⟩ | ⟨h, _⟩
  · exact Or.inl ((mem_beatty_iff φ goldenRatio_pos.le m).1 h)
  · exact Or.inr ((mem_beatty_iff (φ ^ 2) (by positivity) m).1 h)

/-! ### The first column -/

noncomputable def g (i : ℕ) : ℕ := ⌊(i : ℝ) * φ⌋₊ + 1

lemma g_strictMono : StrictMono g := by
  apply strictMono_nat_of_lt_succ
  intro i
  unfold g
  have h0 : (0 : ℝ) ≤ i * φ := mul_nonneg (Nat.cast_nonneg _) goldenRatio_pos.le
  have : ⌊(i : ℝ) * φ + 1⌋₊ ≤ ⌊((i + 1 : ℕ) : ℝ) * φ⌋₊ := by
    apply Nat.floor_le_floor
    push_cast
    nlinarith [one_lt_goldenRatio]
  rw [Nat.floor_add_one h0] at this
  omega

lemma g_mem (i : ℕ) : P (g i) := by
  refine ⟨by unfold g; omega, ?_⟩
  rintro ⟨n, hn, hfn⟩
  rw [f_eq_sq] at hfn
  unfold g at hfn
  rcases Nat.eq_zero_or_pos i with h0 | h0
  · subst h0
    rw [Nat.cast_zero, zero_mul, Nat.floor_zero] at hfn
    have : 1 ≤ ⌊(n : ℝ) * φ ^ 2⌋₊ := by
      apply Nat.le_floor
      have h1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
      have h2 := goldenRatio_sq
      push_cast
      nlinarith [one_lt_goldenRatio, mul_le_mul_of_nonneg_right h1 (sq_nonneg φ)]
    omega
  · exact beatty_disj i n h0 hn (by omega)

lemma P_range (m : ℕ) (hm : P m) : m ∈ Set.range g := by
  obtain ⟨h1, hn⟩ := hm
  rcases Nat.lt_or_ge m 2 with h | h
  · exact ⟨0, by unfold g; simp; omega⟩
  · rcases beatty_cover (m - 1) (by omega) with ⟨k, hk, hkm⟩ | ⟨k, hk, hkm⟩
    · exact ⟨k, by unfold g; omega⟩
    · exact (hn ⟨k, hk, by rw [f_eq_sq]; omega⟩).elim

theorem nth_P (i : ℕ) : Nat.nth P i = ⌊(i : ℝ) * φ⌋₊ + 1 := by
  have hinf : (Set.ofPred P).Infinite :=
    Set.infinite_of_injective_forall_mem g_strictMono.injective g_mem
  have key := Nat.nth_comp_of_strictMono (p := P) (n := i) g_strictMono P_range
    (fun hf => absurd hf hinf)
  have hall : (fun k => P (g k)) = fun _ => True :=
    funext fun k => propext ⟨fun _ => trivial, fun _ => g_mem k⟩
  rw [hall, Nat.nth_true] at key
  rw [← key]; rfl

/-! ### The closed form is closed under f -/

lemma fib_step (m : ℕ) :
    (Nat.fib (m + 2) : ℝ) - Nat.fib m - φ * Nat.fib m = ψ ^ m := by
  rw [Nat.fib_add_two]; push_cast
  have := fib_succ_sub_goldenRatio_mul_fib m
  linarith

lemma X_zero (i : ℕ) : X i 0 = ⌊(i : ℝ) * φ⌋₊ + 1 := by
  have := fl_bounds i
  unfold X b
  simp only [Nat.mul_zero, Nat.zero_add]
  rw [show Nat.fib 2 = 1 from rfl, show Nat.fib 3 = 2 from rfl]
  omega

lemma X_succ (i j : ℕ) : f (X i j) = X i (j + 1) := by
  obtain ⟨hb1, hb2⟩ := fl_bounds i
  set a := ⌊(i : ℝ) * φ⌋₊ with ha
  have hfl1 : (a : ℝ) ≤ i * φ := Nat.floor_le (mul_nonneg (Nat.cast_nonneg _) goldenRatio_pos.le)
  have hfl2 : (i : ℝ) * φ < a + 1 := Nat.lt_floor_add_one _
  set p := b i + 1 with hp
  set q := i - b i with hq
  have hpq1 : p + a = 2 * i + 1 := by simp only [hp, b, ← ha]; omega
  have hpq2 : q + i = a := by simp only [hq, b, ← ha]; omega
  have rp : (p : ℝ) + a = 2 * i + 1 := by exact_mod_cast hpq1
  have rq : (q : ℝ) + i = a := by exact_mod_cast hpq2
  have hX : X i j = p * Nat.fib (2 * j + 2) + q * Nat.fib (2 * j + 3) := rfl
  have hX' : X i (j + 1) = p * Nat.fib (2 * j + 2 + 2) + q * Nat.fib (2 * j + 3 + 2) := by
    unfold X
    rw [show 2 * (j + 1) + 2 = 2 * j + 2 + 2 by ring, show 2 * (j + 1) + 3 = 2 * j + 3 + 2 by ring]
  -- e = X' - X - X φ = ψ^(2j+2) (p + q ψ)
  have he : ((X i (j + 1) : ℕ) : ℝ) - X i j - X i j * φ =
      (ψ ^ 2) ^ (j + 1) * (p + q * ψ) := by
    rw [hX', hX]; push_cast
    have e1 := fib_step (2 * j + 2)
    have e2 := fib_step (2 * j + 3)
    have : (ψ ^ 2) ^ (j + 1) * (p + q * ψ) = p * ψ ^ (2 * j + 2) + q * ψ ^ (2 * j + 3) := by
      rw [← pow_mul]; ring
    rw [this, ← e1, ← e2]; ring
  -- 1 ≤ p + q ψ < φ²
  have hpsi : ψ = 1 - φ := by rw [one_sub_goldenRatio.symm.trans rfl]; linarith [goldenRatio_add_goldenConj]
  have hphi := one_lt_goldenRatio
  have hsq := goldenRatio_sq
  have hc1 : 1 ≤ (p : ℝ) + q * ψ := by
    rw [hpsi]
    have : ((a : ℝ) - i) * φ ≤ i := by nlinarith
    nlinarith
  have hc2 : (p : ℝ) + q * ψ < φ ^ 2 := by
    rw [hpsi]
    have : (i : ℝ) < ((a : ℝ) - i + 1) * φ := by nlinarith
    nlinarith
  have hpsi2 : 0 < ψ ^ 2 := by have := goldenConj_neg; nlinarith
  have hpp : ψ ^ 2 * φ ^ 2 = 1 := by rw [← mul_pow, goldenConj_mul_goldenRatio]; norm_num
  have hpsi21 : ψ ^ 2 ≤ 1 := by nlinarith
  have hpow : (ψ ^ 2) ^ (j + 1) ≤ ψ ^ 2 := pow_le_of_le_one hpsi2.le hpsi21 (by omega)
  have hpowpos : 0 < (ψ ^ 2) ^ (j + 1) := pow_pos hpsi2 _
  have e_pos : 0 < (ψ ^ 2) ^ (j + 1) * (p + q * ψ) := mul_pos hpowpos (by linarith)
  have e_le : (ψ ^ 2) ^ (j + 1) * (p + q * ψ) ≤ 1 := by nlinarith
  -- now compare floors
  rw [f_eq]
  set N := ⌊((X i j : ℕ) : ℝ) * φ⌋₊ with hN
  have n1 : (N : ℝ) ≤ X i j * φ := Nat.floor_le (mul_nonneg (Nat.cast_nonneg _) goldenRatio_pos.le)
  have n2 : (X i j : ℝ) * φ < N + 1 := Nat.lt_floor_add_one _
  have c1 : (N : ℝ) + X i j < X i (j + 1) := by linarith
  have c2 : ((X i (j + 1) : ℕ) : ℝ) < N + X i j + 2 := by linarith
  have d1 : N + X i j < X i (j + 1) := by exact_mod_cast c1
  have d2 : X i (j + 1) < N + X i j + 2 := by exact_mod_cast c2
  omega

/-- Main theorem: the dispersion of f(n) = ⌊nφ + n + 1⌋ has the closed form
(b(i)+1) F(2j) + (i - b(i)) F(2j+1) (entry's column index j ≥ 1),
with b(i) = 2i - ⌊iφ⌋. -/
theorem A132827_dispersion (i j : ℕ) :
    disp i j = (b i + 1) * Nat.fib (2 * (j + 1)) + (i - b i) * Nat.fib (2 * (j + 1) + 1) := by
  have : disp i j = X i j := by
    induction j with
    | zero => simp [disp, nth_P, X_zero]
    | succ j ih =>
      rw [disp, Function.iterate_succ_apply', ← disp, ih, X_succ]
  rw [this]; rfl

/-! ### The entry's data and its FORMULA -/

lemma floor_phi_eq (n k : ℕ) (h0 : n ≤ 2 * k) (h1 : (2 * k - n) ^ 2 ≤ 5 * n ^ 2)
    (h2 : 5 * n ^ 2 < (2 * k + 2 - n) ^ 2) : ⌊(n : ℝ) * φ⌋₊ = k := by
  have s0 : (0 : ℝ) ≤ √5 := Real.sqrt_nonneg _
  have s2 : √5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have r1 : ((2 * k : ℝ) - n) ^ 2 ≤ 5 * n ^ 2 := by
    have : ((2 * k - n : ℕ) : ℝ) = 2 * k - n := by push_cast [Nat.cast_sub h0]; ring
    rw [← this]; exact_mod_cast h1
  have r2 : 5 * (n : ℝ) ^ 2 < (2 * k + 2 - n) ^ 2 := by
    have : ((2 * k + 2 - n : ℕ) : ℝ) = 2 * k + 2 - n := by push_cast [Nat.cast_sub (by omega : n ≤ 2 * k + 2)]; ring
    rw [← this]; exact_mod_cast h2
  have hk : (n : ℝ) ≤ 2 * k := by exact_mod_cast h0
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  rw [Nat.floor_eq_iff (by positivity), Real.goldenRatio]
  constructor
  · nlinarith [mul_nonneg s0 hn]
  · nlinarith [mul_nonneg s0 hn]

lemma fl_small : ∀ i : ℕ, i < 8 → ⌊(i : ℝ) * φ⌋₊ = [0, 1, 3, 4, 6, 8, 9, 11].getD i 0 := by
  intro i hi
  interval_cases i <;> exact floor_phi_eq _ _ (by norm_num) (by norm_num) (by norm_num)

/-- The array read by antidiagonals: (row, column from 0) of the N-th term, N < 36. -/
def antidiag : List (ℕ × ℕ) :=
  ((List.range 8).flatMap fun s => (List.range (s + 1)).map fun i => (i, s - i)).take 36

/-- The 36 data terms of A132827. -/
def data : List ℕ := [1, 3, 2, 8, 6, 4, 21, 16, 11, 5, 55, 42, 29, 14, 7, 144, 110, 76, 37,
  19, 9, 377, 288, 199, 97, 50, 24, 10, 987, 754, 521, 254, 131, 63, 27, 12]

def Y (a i j : ℕ) : ℕ :=
  (2 * i - a + 1) * Nat.fib (2 * (j + 1)) + (i - (2 * i - a)) * Nat.fib (2 * (j + 1) + 1)

theorem A132827_data : antidiag.map (fun p => disp p.1 p.2) = data := by
  have hb : ∀ p ∈ antidiag, p.1 < 8 := by decide
  rw [List.map_congr_left (g := fun p => Y ([0, 1, 3, 4, 6, 8, 9, 11].getD p.1 0) p.1 p.2)]
  · decide
  · intro p hp
    rw [A132827_dispersion, b, fl_small p.1 (hb p hp)]; rfl

/-- A005206 (Hofstadter G) by its definition G(0) = 0, G(n) = n - G(G(n-1)). -/
def gl : ℕ → List ℕ
  | 0 => [0]
  | n + 1 => let l := gl n; l ++ [(n + 1) - l.getD (l.getD n 0) 0]

def hofG (n : ℕ) : ℕ := (gl n).getD n 0

/-- The entry's FORMULA with b = A005206 (entry's column index j ≥ 1). -/
def entryFormula (i j : ℕ) : ℕ :=
  (hofG i + 1) * Nat.fib (2 * j) + (i - hofG i) * Nat.fib (2 * j + 1)

theorem entryFormula_wrong : entryFormula 4 1 = 6 ∧ disp 4 0 = 7 := by
  refine ⟨by decide, ?_⟩
  rw [A132827_dispersion, b, fl_small 4 (by norm_num)]; rfl
