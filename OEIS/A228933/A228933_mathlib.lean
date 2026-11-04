/-
OEIS A228933, Mathlib proof.

The optimal ascending continued fraction (OACF) of A228929: z_0 = x - ⌊x⌋,
r_k = round(1/|z_k|), a(k+1) = sign(z_k) r_k, z_(k+1) = |z_k| r_k - 1
(`A228933_z`, `A228933_a`; Mathlib `round`; no half ever occurs here).

Main theorem `A228933_main`: for x = 1/φ (Mathlib `Real.goldenRatio`),
a(1) = 2, a(2) = 4, a(3) = -18, a(4) = 322, a(n) > 0 for n ≥ 4 and
a(n) = a(n-1)^2 - 2 for every n ≥ 4. This is Artico's conjecture (from the
fourth term on the recurrence a(n) = a(n-1)^2 - 2 holds).

Proof: z_1 = √5 - 2 = φ^(-3), r_1 = round(√5 + 2) = 4, z_2 = 4√5 - 9 = -1/U
with U = 9 + 4√5 = φ^6, U + 1/U = 18, z_3 = 1/U^2; from there the lemma
`A228933_step` (|z_k| = 1/V, V ≥ 2, V + 1/V = t ∈ ℤ gives r_k = t and
z_(k+1) = 1/V^2) is iterated in `A228933_chain` / `A228933_rec`.

Not checked: nothing.
-/
import Mathlib

/-- The OACF remainders of A228929: z_0 = x - ⌊x⌋, z_(k+1) = |z_k| r_k - 1
with r_k = round(1/|z_k|). -/
noncomputable def A228933_z (x : ℝ) : ℕ → ℝ
  | 0 => x - ⌊x⌋
  | k + 1 => |A228933_z x k| * (round (1 / |A228933_z x k|) : ℝ) - 1

/-- The OACF terms: a(k + 1) = sign(z_k) r_k (a(0) is unused and set to 0). -/
noncomputable def A228933_a (x : ℝ) : ℕ → ℤ
  | 0 => 0
  | k + 1 => if 0 ≤ A228933_z x k then round (1 / |A228933_z x k|) else -round (1 / |A228933_z x k|)

theorem A228933_round_add {V : ℝ} (hV : 2 ≤ V) {t : ℤ} (ht : V + 1 / V = t) : round V = t := by
  have hV0 : 0 < V := by linarith
  have h1 : 0 < 1 / V := by positivity
  have h2 : 1 / V ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hV
  rw [round_eq, Int.floor_eq_iff]
  constructor <;> linarith

theorem A228933_round_sub {V : ℝ} (hV : 2 < V) {t : ℤ} (ht : V - 1 / V = t) : round V = t := by
  have hV0 : 0 < V := by linarith
  have h1 : 0 < 1 / V := by positivity
  have h2 : 1 / V < 1 / 2 := one_div_lt_one_div_of_lt (by norm_num) hV
  rw [round_eq, Int.floor_eq_iff]
  constructor <;> linarith

/-- One step from z_k = ± 1/V with V + 1/V = t ∈ ℤ: r_k = t and z_(k+1) = 1/V^2. -/
theorem A228933_step (x : ℝ) (k : ℕ) {V : ℝ} (hV : 2 ≤ V) {t : ℤ} (ht : V + 1 / V = t)
    (hz : |A228933_z x k| = 1 / V) :
    round (1 / |A228933_z x k|) = t ∧ A228933_z x (k + 1) = 1 / V ^ 2 := by
  have hV0 : V ≠ 0 := by positivity
  have hr : round (1 / |A228933_z x k|) = t := by
    rw [hz, one_div_one_div]
    exact A228933_round_add hV ht
  refine ⟨hr, ?_⟩
  show |A228933_z x k| * (round (1 / |A228933_z x k|) : ℝ) - 1 = 1 / V ^ 2
  rw [hr, ← ht, hz]
  field_simp
  ring

/-- From z_k = 1/V (V ≥ 2, V + 1/V ∈ ℤ) on, every term is positive and
a(j + 1) = a(j)^2 - 2. -/
theorem A228933_chain (x : ℝ) (k : ℕ) {V : ℝ} (hV : 2 ≤ V) {t : ℤ} (ht : V + 1 / V = t)
    (hz : A228933_z x k = 1 / V) :
    ∀ m, ∃ W : ℝ, 2 ≤ W ∧ A228933_z x (k + m) = 1 / W ∧ W + 1 / W = A228933_a x (k + m + 1) := by
  have hpos : ∀ {W : ℝ}, 2 ≤ W → 0 ≤ 1 / W := by
    intro W h
    have : (0 : ℝ) < W := by linarith
    positivity
  have hterm : ∀ {W : ℝ} {j : ℕ} {u : ℤ}, 2 ≤ W → W + 1 / W = u → A228933_z x j = 1 / W →
      A228933_a x (j + 1) = u := by
    intro W j u hW hu hzj
    have habs : |A228933_z x j| = 1 / W := by rw [hzj, abs_of_nonneg (hpos hW)]
    show (if 0 ≤ A228933_z x j then _ else _) = u
    rw [ite_eq_left (by rw [hzj]; exact hpos hW)]
    exact (A228933_step x j hW hu habs).1
  intro m
  induction m with
  | zero => exact ⟨V, hV, hz, by rw [hterm hV ht hz]; exact ht⟩
  | succ m ih =>
    obtain ⟨W, hW, hzW, hWt⟩ := ih
    have habs : |A228933_z x (k + m)| = 1 / W := by rw [hzW, abs_of_nonneg (hpos hW)]
    have hnext := (A228933_step x (k + m) hW hWt habs).2
    have hW2 : 2 ≤ W ^ 2 := by nlinarith
    have hW0 : W ≠ 0 := by positivity
    have hu : W ^ 2 + 1 / W ^ 2 = ((A228933_a x (k + m + 1) ^ 2 - 2 : ℤ) : ℝ) := by
      push_cast
      rw [← hWt]
      field_simp
      ring
    refine ⟨W ^ 2, hW2, by rw [← add_assoc]; exact hnext, ?_⟩
    rw [hterm hW2 hu (by rw [← add_assoc]; exact hnext)]
    exact hu

theorem A228933_rec (x : ℝ) (k : ℕ) {V : ℝ} (hV : 2 ≤ V) {t : ℤ} (ht : V + 1 / V = t)
    (hz : A228933_z x k = 1 / V) (m : ℕ) :
    0 < A228933_a x (k + m + 1) ∧ A228933_a x (k + m + 2) = A228933_a x (k + m + 1) ^ 2 - 2 := by
  obtain ⟨W, hW, hzW, hWt⟩ := A228933_chain x k hV ht hz m
  obtain ⟨W', hW', hzW', hWt'⟩ := A228933_chain x k hV ht hz (m + 1)
  have hW0 : 0 < W := by linarith
  have hnext := (A228933_step x (k + m) hW hWt (by rw [hzW, abs_of_nonneg (by positivity)])).2
  rw [← add_assoc, hnext] at hzW'
  have hW'0 : 0 < W' := by linarith
  have hWW : W' = W ^ 2 := by
    have := congrArg (fun r => 1 / r) hzW'
    simp only [one_div_one_div] at this
    exact this.symm
  constructor
  · have : (0 : ℝ) < A228933_a x (k + m + 1) := by rw [← hWt]; positivity
    exact_mod_cast this
  · have h : ((A228933_a x (k + m + 2) : ℤ) : ℝ) = ((A228933_a x (k + m + 1) ^ 2 - 2 : ℤ) : ℝ) := by
      rw [show k + m + 2 = k + (m + 1) + 1 by ring, ← hWt', hWW]
      push_cast
      rw [← hWt]
      field_simp
      ring
    exact_mod_cast h

theorem A228933_main :
    let a := A228933_a (1 / Real.goldenRatio)
    a 1 = 2 ∧ a 2 = 4 ∧ a 3 = -18 ∧ a 4 = 322 ∧
    (∀ n ≥ 4, 0 < a n) ∧ (∀ n ≥ 4, a n = a (n - 1) ^ 2 - 2) := by
  intro a
  set x := 1 / Real.goldenRatio with hx
  set s := Real.sqrt 5 with hs
  have hs2 : s ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg 5
  have hsl : 2.236 < s := by nlinarith
  have hsu : s < 2.237 := by nlinarith
  have hxs : x = (s - 1) / 2 := by
    rw [hx, Real.goldenRatio, ← hs]
    field_simp [show 1 + s ≠ 0 by linarith]
    nlinarith
  have hfl : ⌊x⌋ = 0 := by
    rw [Int.floor_eq_zero_iff, hxs]
    constructor <;> linarith
  have hz0 : A228933_z x 0 = (s - 1) / 2 := by
    show x - ⌊x⌋ = (s - 1) / 2
    rw [hfl, hxs]
    simp
  have habs0 : |A228933_z x 0| = (s - 1) / 2 := by rw [hz0, abs_of_pos (by linarith)]
  have hr0 : round (1 / |A228933_z x 0|) = 2 := by
    have : 1 / |A228933_z x 0| = (s + 1) / 2 := by
      rw [habs0]
      field_simp [show s - 1 ≠ 0 by linarith]
      nlinarith
    rw [this, round_eq, Int.floor_eq_iff]
    constructor <;> push_cast <;> linarith
  have ha1 : a 1 = 2 := by
    show (if 0 ≤ A228933_z x 0 then _ else _) = 2
    rw [ite_eq_left (by rw [hz0]; linarith), hr0]
  have hz1 : A228933_z x 1 = s - 2 := by
    show |A228933_z x 0| * (round (1 / |A228933_z x 0|) : ℝ) - 1 = s - 2
    rw [hr0, habs0]
    push_cast
    ring
  have habs1 : |A228933_z x 1| = s - 2 := by rw [hz1, abs_of_pos (by linarith)]
  have hr1 : round (1 / |A228933_z x 1|) = 4 := by
    have hinv : 1 / (s + 2) = s - 2 := by
      field_simp [show s + 2 ≠ 0 by linarith]
      nlinarith
    have : 1 / |A228933_z x 1| = s + 2 := by
      rw [habs1, ← hinv, one_div_one_div]
    rw [this]
    exact A228933_round_sub (by linarith) (by rw [hinv]; push_cast; ring)
  have ha2 : a 2 = 4 := by
    show (if 0 ≤ A228933_z x 1 then _ else _) = 4
    rw [ite_eq_left (by rw [hz1]; linarith), hr1]
  have hz2 : A228933_z x 2 = 4 * s - 9 := by
    show |A228933_z x 1| * (round (1 / |A228933_z x 1|) : ℝ) - 1 = 4 * s - 9
    rw [hr1, habs1]
    push_cast
    ring
  set U := 9 + 4 * s with hU
  have hU2 : 2 ≤ U := by linarith
  have hU0 : U ≠ 0 := by linarith
  have hUinv : 1 / U = 9 - 4 * s := by
    field_simp
    nlinarith
  have hUt : U + 1 / U = ((18 : ℤ) : ℝ) := by rw [hUinv, hU]; push_cast; ring
  have habs2 : |A228933_z x 2| = 1 / U := by
    rw [hz2, abs_of_neg (by linarith), hUinv]
    ring
  obtain ⟨hr2, hz3⟩ := A228933_step x 2 hU2 hUt habs2
  have ha3 : a 3 = -18 := by
    show (if 0 ≤ A228933_z x 2 then _ else _) = -18
    rw [ite_eq_right (by rw [hz2]; linarith), hr2]
  have hV2 : 2 ≤ U ^ 2 := by nlinarith
  have hVt : U ^ 2 + 1 / U ^ 2 = ((322 : ℤ) : ℝ) := by
    have : U ^ 2 + 1 / U ^ 2 = (U + 1 / U) ^ 2 - 2 := by field_simp; ring
    rw [this, hUt]
    norm_num
  have hrec := A228933_rec x 3 hV2 hVt hz3
  obtain ⟨W, hW, hzW, hWt⟩ := A228933_chain x 3 hV2 hVt hz3 0
  have hWU : W = U ^ 2 := by
    rw [add_zero, hz3] at hzW
    have := congrArg (fun r => 1 / r) hzW
    simpa using this.symm
  have ha4 : a 4 = 322 := by
    have : ((a 4 : ℤ) : ℝ) = ((322 : ℤ) : ℝ) := by
      rw [← hVt, ← hWU, hWt]
    exact_mod_cast this
  refine ⟨ha1, ha2, ha3, ha4, ?_, ?_⟩
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = 3 + m + 1 := ⟨n - 4, by omega⟩
    exact (hrec m).1
  · intro n hn
    rcases Nat.eq_or_lt_of_le hn with rfl | hn
    · rw [show 4 - 1 = 3 from rfl, ha3, ha4]
      norm_num
    · obtain ⟨m, rfl⟩ : ∃ m, n = 3 + m + 2 := ⟨n - 5, by omega⟩
      rw [show 3 + m + 2 - 1 = 3 + m + 1 by omega]
      exact (hrec m).2
