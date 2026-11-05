/-
OEIS A228934, Mathlib proof.

The optimal ascending continued fraction (OACF) of A228929: z_0 = x - ⌊x⌋,
r_k = round(1/|z_k|), a(k+1) = sign(z_k) r_k, z_(k+1) = |z_k| r_k - 1
(`A228934_z`, `A228934_a`; Mathlib `round`; no half ever occurs here).

Main theorem `A228934_main`: for x = √44 - 6,
a(1) = 2, a(2) = 4, a(3) = 15, a(4) = -99, a(n) < 0 for n ≥ 4, and for
every n ≥ 3: a(2n) = 4 a(2n-1) - 4 and a(2n+1) = -2 a(2n-1)^2 + 1.
This is Artico's conjecture in A228934.

Proof: with ε = 199 + 30√44 (1/ε = 199 - 30√44), z_3 = -4/ε and
z_4 = 1/ε^2 - 2/ε. Two-step invariant (`A228934_stepA`, `A228934_stepB`):
if z_k = 1/G^2 - 2/G with G ≥ 11 and G + 1/G = 2s (s ∈ ℤ), then
r_k = s, z_(k+1) = -(G-1)^2/(2G^3), r_(k+1) = 4s + 4 and
z_(k+2) = 1/G^4 - 2/G^2; so a(k+1) = -s, a(k+2) = -(4s+4), and the
invariant holds again with G^2 and s' = 2s^2 - 1 (`A228934_chain`, with
G = ε^(2^m), s = `A228934_S m`).

Not checked: nothing (the statement is checked over ℝ for x = √44 - 6).
-/
import Mathlib

/-- The OACF remainders of A228929: z_0 = x - ⌊x⌋, z_(k+1) = |z_k| r_k - 1
with r_k = round(1/|z_k|). -/
noncomputable def A228934_z (x : ℝ) : ℕ → ℝ
  | 0 => x - ⌊x⌋
  | k + 1 => |A228934_z x k| * (round (1 / |A228934_z x k|) : ℝ) - 1

/-- The OACF terms: a(k + 1) = sign(z_k) r_k (a(0) is unused and set to 0). -/
noncomputable def A228934_a (x : ℝ) : ℕ → ℤ
  | 0 => 0
  | k + 1 => if 0 ≤ A228934_z x k then round (1 / |A228934_z x k|) else -round (1 / |A228934_z x k|)

/-- s_0 = 199, s_(m+1) = 2 s_m^2 - 1, so that ε^(2^m) + ε^(-2^m) = 2 s_m. -/
def A228934_S : ℕ → ℤ
  | 0 => 199
  | m + 1 => 2 * A228934_S m ^ 2 - 1

/-- round y = t whenever t - 1/2 ≤ y < t + 1/2. -/
theorem A228934_round_of {y : ℝ} {t : ℤ} (h1 : (t : ℝ) - 1 / 2 ≤ y) (h2 : y < t + 1 / 2) :
    round y = t := by
  rw [round_eq, Int.floor_eq_iff]
  constructor <;> linarith

theorem A228934_stepA (x : ℝ) (k : ℕ) {G : ℝ} (hG : 11 ≤ G) {s : ℤ} (hs : G + 1 / G = 2 * s)
    (hz : A228934_z x k = 1 / G ^ 2 - 2 / G) :
    A228934_z x (k + 1) = -(G - 1) ^ 2 / (2 * G ^ 3) ∧ A228934_a x (k + 1) = -s := by
  have hG0 : 0 < G := by linarith
  have hsR : (s : ℝ) = (G ^ 2 + 1) / (2 * G) := by
    field_simp
    field_simp at hs
    linarith
  have hneg : A228934_z x k < 0 := by
    rw [hz]
    have : 1 / G ^ 2 - 2 / G = (1 - 2 * G) / G ^ 2 := by field_simp
    rw [this]
    apply div_neg_of_neg_of_pos <;> nlinarith
  have habs : |A228934_z x k| = (2 * G - 1) / G ^ 2 := by
    rw [abs_of_neg hneg, hz]
    field_simp
    ring
  have h2G : 0 < 2 * G - 1 := by linarith
  have hkey : 1 / |A228934_z x k| = s + (G - 1) ^ 2 / (2 * G * (2 * G - 1)) := by
    rw [habs, hsR]
    field_simp
    ring
  have hr : round (1 / |A228934_z x k|) = s := by
    apply A228934_round_of
    · rw [hkey]
      have : 0 ≤ (G - 1) ^ 2 / (2 * G * (2 * G - 1)) := by positivity
      linarith
    · rw [hkey]
      have : (G - 1) ^ 2 / (2 * G * (2 * G - 1)) < 1 / 2 := by
        rw [div_lt_iff₀ (by positivity)]
        nlinarith
      linarith
  constructor
  · show |A228934_z x k| * (round (1 / |A228934_z x k|) : ℝ) - 1 = _
    rw [hr, habs, hsR]
    field_simp
    ring
  · show (if 0 ≤ A228934_z x k then _ else _) = -s
    rw [ite_eq_right (by linarith), hr]

theorem A228934_stepB (x : ℝ) (k : ℕ) {G : ℝ} (hG : 11 ≤ G) {s : ℤ} (hs : G + 1 / G = 2 * s)
    (hz : A228934_z x k = -(G - 1) ^ 2 / (2 * G ^ 3)) :
    A228934_z x (k + 1) = 1 / (G ^ 2) ^ 2 - 2 / G ^ 2 ∧ A228934_a x (k + 1) = -(4 * s + 4) := by
  have hG0 : 0 < G := by linarith
  have hsR : (s : ℝ) = (G ^ 2 + 1) / (2 * G) := by
    field_simp
    field_simp at hs
    linarith
  have hneg : A228934_z x k < 0 := by
    rw [hz, neg_div]
    have : 0 < (G - 1) ^ 2 / (2 * G ^ 3) := by
      apply div_pos <;> nlinarith
    linarith
  have habs : |A228934_z x k| = (G - 1) ^ 2 / (2 * G ^ 3) := by
    rw [abs_of_neg hneg, hz, neg_div, neg_neg]
  have hG1 : 0 < G - 1 := by linarith
  have hkey : 1 / |A228934_z x k| = ((4 * s + 4 : ℤ) : ℝ) + (4 * G ^ 2 - 2) / (G * (G - 1) ^ 2) := by
    rw [habs]
    push_cast
    rw [hsR]
    field_simp
    ring
  have hr : round (1 / |A228934_z x k|) = 4 * s + 4 := by
    apply A228934_round_of
    · rw [hkey]
      have : 0 ≤ (4 * G ^ 2 - 2) / (G * (G - 1) ^ 2) := by
        apply div_nonneg <;> nlinarith
      linarith
    · rw [hkey]
      have : (4 * G ^ 2 - 2) / (G * (G - 1) ^ 2) < 1 / 2 := by
        rw [div_lt_iff₀ (by positivity)]
        nlinarith [mul_pos hG0 hG0]
      linarith
  constructor
  · show |A228934_z x k| * (round (1 / |A228934_z x k|) : ℝ) - 1 = _
    rw [hr, habs]
    push_cast
    rw [hsR]
    field_simp
    ring
  · show (if 0 ≤ A228934_z x k then _ else _) = -(4 * s + 4)
    rw [ite_eq_right (by linarith), hr]

/-- From z_k = 1/ε^2 - 2/ε on (ε ≥ 11, ε + 1/ε = 398): with G_m = ε^(2^m),
z_(k+2m) = 1/G_m^2 - 2/G_m, a(k+2m+1) = -s_m, a(k+2m+2) = -(4 s_m + 4). -/
theorem A228934_chain (x : ℝ) (k : ℕ) {e : ℝ} (he : 11 ≤ e) (het : e + 1 / e = 2 * 199)
    (hz : A228934_z x k = 1 / e ^ 2 - 2 / e) (m : ℕ) :
    11 ≤ e ^ (2 ^ m) ∧ e ^ (2 ^ m) + 1 / e ^ (2 ^ m) = 2 * A228934_S m ∧
    A228934_z x (k + 2 * m) = 1 / (e ^ (2 ^ m)) ^ 2 - 2 / e ^ (2 ^ m) ∧
    A228934_a x (k + 2 * m + 1) = -A228934_S m ∧
    A228934_a x (k + 2 * m + 2) = -(4 * A228934_S m + 4) := by
  induction m with
  | zero =>
    simp only [pow_zero, pow_one, mul_zero, add_zero, A228934_S]
    obtain ⟨hz1, ha1⟩ := A228934_stepA x k (s := 199) he (by push_cast; linarith) hz
    obtain ⟨_, ha2⟩ := A228934_stepB x (k + 1) (s := 199) he (by push_cast; linarith) hz1
    exact ⟨he, by push_cast; linarith, hz, ha1, ha2⟩
  | succ m ih =>
    obtain ⟨hG, hGs, hzG, -, -⟩ := ih
    set G := e ^ (2 ^ m) with hGdef
    have hGG : e ^ (2 ^ (m + 1)) = G ^ 2 := by rw [pow_succ, pow_mul]
    have hG0 : 0 < G := by linarith
    obtain ⟨hz1, -⟩ := A228934_stepA x (k + 2 * m) hG hGs hzG
    obtain ⟨hz2, -⟩ := A228934_stepB x (k + 2 * m + 1) hG hGs hz1
    have hG2 : 11 ≤ G ^ 2 := by nlinarith
    have hG2s : G ^ 2 + 1 / G ^ 2 = 2 * ((A228934_S (m + 1) : ℤ) : ℝ) := by
      simp only [A228934_S]
      push_cast
      have : G ^ 2 + 1 / G ^ 2 = (G + 1 / G) ^ 2 - 2 := by field_simp; ring
      rw [this, hGs]
      ring
    have hidx : k + 2 * (m + 1) = k + 2 * m + 1 + 1 := by ring
    rw [hidx] at *
    obtain ⟨hz3, ha3⟩ := A228934_stepA x (k + 2 * m + 1 + 1) hG2 hG2s hz2
    obtain ⟨_, ha4⟩ := A228934_stepB x (k + 2 * m + 1 + 1 + 1) hG2 hG2s hz3
    rw [hGG]
    exact ⟨hG2, hG2s, hz2, ha3, ha4⟩

theorem A228934_S_pos (m : ℕ) : 0 < A228934_S m := by
  induction m with
  | zero => decide
  | succ m ih =>
    simp only [A228934_S]
    nlinarith

theorem A228934_main :
    let a := A228934_a (Real.sqrt 44 - 6)
    a 1 = 2 ∧ a 2 = 4 ∧ a 3 = 15 ∧ a 4 = -99 ∧
    (∀ n ≥ 4, a n < 0) ∧
    (∀ n ≥ 3, a (2 * n) = 4 * a (2 * n - 1) - 4 ∧ a (2 * n + 1) = -2 * a (2 * n - 1) ^ 2 + 1) := by
  intro a
  set x := Real.sqrt 44 - 6 with hx
  set s := Real.sqrt 44 with hs
  have hs2 : s ^ 2 = 44 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg 44
  have hsl : 6.6332 < s := by nlinarith
  have hsu : s < 6.6333 := by nlinarith
  have hfl : ⌊x⌋ = 0 := by
    rw [Int.floor_eq_iff, hx]
    constructor <;> push_cast <;> linarith
  have hz0 : A228934_z x 0 = s - 6 := by
    show x - ⌊x⌋ = s - 6
    rw [hfl, hx]
    push_cast
    ring
  -- step 0: 1/(s - 6) = (s + 6)/8
  --
  have habs0 : |A228934_z x 0| = s - 6 := by rw [hz0, abs_of_pos (by linarith)]
  have hr0 : round (1 / |A228934_z x 0|) = 2 := by
    have : 1 / |A228934_z x 0| = (s + 6) / 8 := by
      rw [habs0]
      field_simp [show s - 6 ≠ 0 by linarith]
      nlinarith
    rw [this]
    apply A228934_round_of <;> push_cast <;> linarith
  have ha1 : a 1 = 2 := by
    show (if 0 ≤ A228934_z x 0 then _ else _) = 2
    rw [ite_eq_left (by rw [hz0]; linarith), hr0]
  have hz1 : A228934_z x 1 = 2 * s - 13 := by
    show |A228934_z x 0| * (round (1 / |A228934_z x 0|) : ℝ) - 1 = _
    rw [hr0, habs0]
    push_cast
    ring
  -- step 1: 1/(2s - 13) = (2s + 13)/7
  --
  have habs1 : |A228934_z x 1| = 2 * s - 13 := by rw [hz1, abs_of_pos (by linarith)]
  have hr1 : round (1 / |A228934_z x 1|) = 4 := by
    have : 1 / |A228934_z x 1| = (2 * s + 13) / 7 := by
      rw [habs1]
      field_simp [show 2 * s - 13 ≠ 0 by linarith]
      nlinarith
    rw [this]
    apply A228934_round_of <;> push_cast <;> linarith
  have ha2 : a 2 = 4 := by
    show (if 0 ≤ A228934_z x 1 then _ else _) = 4
    rw [ite_eq_left (by rw [hz1]; linarith), hr1]
  have hz2 : A228934_z x 2 = 8 * s - 53 := by
    show |A228934_z x 1| * (round (1 / |A228934_z x 1|) : ℝ) - 1 = _
    rw [hr1, habs1]
    push_cast
    ring
  -- step 2: 1/(8s - 53) = (8s + 53)/7
  --
  have habs2 : |A228934_z x 2| = 8 * s - 53 := by rw [hz2, abs_of_pos (by linarith)]
  have hr2 : round (1 / |A228934_z x 2|) = 15 := by
    have : 1 / |A228934_z x 2| = (8 * s + 53) / 7 := by
      rw [habs2]
      field_simp [show 8 * s - 53 ≠ 0 by linarith]
      nlinarith
    rw [this]
    apply A228934_round_of <;> push_cast <;> linarith
  have ha3 : a 3 = 15 := by
    show (if 0 ≤ A228934_z x 2 then _ else _) = 15
    rw [ite_eq_left (by rw [hz2]; linarith), hr2]
  have hz3 : A228934_z x 3 = 120 * s - 796 := by
    show |A228934_z x 2| * (round (1 / |A228934_z x 2|) : ℝ) - 1 = _
    rw [hr2, habs2]
    push_cast
    ring
  -- step 3: z_3 < 0, 1/|z_3| = (199 + 30s)/4 just below 99.5
  --
  have habs3 : |A228934_z x 3| = 796 - 120 * s := by
    rw [hz3, abs_of_neg (by linarith)]
    ring
  have hr3 : round (1 / |A228934_z x 3|) = 99 := by
    have : 1 / |A228934_z x 3| = (199 + 30 * s) / 4 := by
      rw [habs3]
      field_simp [show 796 - 120 * s ≠ 0 by linarith]
      nlinarith
    rw [this]
    apply A228934_round_of <;> push_cast <;> linarith
  have ha4 : a 4 = -99 := by
    show (if 0 ≤ A228934_z x 3 then _ else _) = -99
    rw [ite_eq_right (by rw [hz3]; linarith), hr3]
  have hz4 : A228934_z x 4 = 78803 - 11880 * s := by
    show |A228934_z x 3| * (round (1 / |A228934_z x 3|) : ℝ) - 1 = _
    rw [hr3, habs3]
    push_cast
    ring
  -- ε = 199 + 30s, 1/ε = 199 - 30s, z_4 = 1/ε^2 - 2/ε
  --
  set e := 199 + 30 * s with he
  have he11 : 11 ≤ e := by linarith
  have he0 : e ≠ 0 := by linarith
  have heinv : 1 / e = 199 - 30 * s := by
    field_simp
    nlinarith
  have het : e + 1 / e = 2 * 199 := by rw [heinv, he]; ring
  have hz4e : A228934_z x 4 = 1 / e ^ 2 - 2 / e := by
    have h2 : 1 / e ^ 2 = (1 / e) ^ 2 := by rw [one_div_pow]
    rw [hz4, h2, div_eq_mul_one_div 2 e, heinv]
    nlinarith
  have hch := A228934_chain x 4 he11 het hz4e
  refine ⟨ha1, ha2, ha3, ha4, ?_, ?_⟩
  · intro n hn
    rcases Nat.eq_or_lt_of_le hn with rfl | hn
    · rw [ha4]; norm_num
    obtain ⟨m, rfl | rfl⟩ : ∃ m, n = 4 + 2 * m + 1 ∨ n = 4 + 2 * m + 2 :=
      ⟨(n - 5) / 2, by omega⟩
    · change A228934_a x (4 + 2 * m + 1) < 0
      rw [(hch m).2.2.2.1]
      linarith [A228934_S_pos m]
    · change A228934_a x (4 + 2 * m + 2) < 0
      rw [(hch m).2.2.2.2]
      linarith [A228934_S_pos m]
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
    have e1 : 2 * (m + 3) = 4 + 2 * m + 2 := by ring
    have e2 : 2 * (m + 3) - 1 = 4 + 2 * m + 1 := by omega
    have e3 : 2 * (m + 3) + 1 = 4 + 2 * (m + 1) + 1 := by ring
    change A228934_a x _ = 4 * A228934_a x _ - 4 ∧ A228934_a x _ = -2 * A228934_a x _ ^ 2 + 1
    rw [e3, e2, e1, (hch m).2.2.2.1, (hch m).2.2.2.2, (hch (m + 1)).2.2.2.1]
    simp only [A228934_S]
    constructor <;> ring
