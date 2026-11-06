/-
OEIS A078122: the lower triangular matrix M with M(k,0) = M(k,k) = 1 and
[M^3](i,j) = M(i+1,j+1). Conjecture (entry text): the sum of row n is A078125(n), the number of
partitions of 3^n into powers of 3.

Definitions.
* `cnt S hi lo`: number of partitions of S into parts 3^e with lo ≤ e ≤ hi, counted as weakly
  decreasing lists of exponents (first part chosen, then the rest with exponents ≤ it).
* `A078125 n = cnt (3^n) (3^n) 0`: partitions of 3^n into powers of 3 (exponents ≤ 3^n, which
  includes every power ≤ 3^n).
* `E S h lo`: those partitions of S whose largest part is exactly 3^h.
* `N n k = E (3^n) (n-k) 0` for k ≤ n, else 0.
* `IsA078122 M`: M lower triangular, M k 0 = 1, M k k = 1, and
  M (i+1) (j+1) = Σ_{a,b ≤ i} M i a * M a b * M b j (this is [M^3](i,j) for lower triangular M).

Main theorems.
* `N_spec`: N satisfies `IsA078122` (so the matrix exists).
* `eq_N`: every M with `IsA078122 M` equals N.
* `A078122_rowsum`: for such M, Σ_{k ≤ n} M n k = A078125 n.

Route: `split` (a partition of T + R whose parts divide T splits at running sum T),
`scale` (exponents shifted by s ↔ sums multiplied by 3^s), `cube` (two splits of 3^(i+1)).

Not checked in this file: agreement with the OEIS data terms (certificate/check.py).
-/
import Mathlib

open Finset

namespace A078122

def cnt (S hi lo : ℕ) : ℕ :=
  if hS : S = 0 then 1 else
    ∑ e ∈ (Icc lo hi).attach, if 3 ^ e.1 ≤ S then cnt (S - 3 ^ e.1) e.1 lo else 0
termination_by S
decreasing_by
  have : 0 < 3 ^ e.1 := by positivity
  omega

theorem itT {p : Prop} [Decidable p] {α : Type} (h : p) (a b : α) :
    (if p then a else b) = a := by simp [h]

theorem itF {p : Prop} [Decidable p] {α : Type} (h : ¬ p) (a b : α) :
    (if p then a else b) = b := by simp [h]

def E (S h lo : ℕ) : ℕ := if 3 ^ h ≤ S then cnt (S - 3 ^ h) h lo else 0

theorem cnt_zero (hi lo : ℕ) : cnt 0 hi lo = 1 := by
  rw [cnt]; simp

theorem cnt_pos {S : ℕ} (hS : S ≠ 0) (hi lo : ℕ) :
    cnt S hi lo = ∑ e ∈ Icc lo hi, E S e lo := by
  rw [cnt]; simp only [hS, dite_false]
  exact Finset.sum_attach (Icc lo hi) (fun e => E S e lo)

/-- A partition of T + R (R ≥ 1) with exponents ≤ hi, where 3^hi ∣ T, splits after the parts
summing to T; the rest has largest part 3^m, the first block has exponents in [m, hi]. -/
theorem split (R : ℕ) (hR : R ≠ 0) (lo : ℕ) : ∀ T hi, 3 ^ hi ∣ T →
    cnt (T + R) hi lo = ∑ m ∈ Icc lo hi, cnt T hi m * E R m lo := by
  intro T
  induction T using Nat.strong_induction_on with
  | _ T ih =>
    intro hi hT
    by_cases h0 : T = 0
    · subst h0
      simp only [zero_add, cnt_zero, one_mul]
      exact cnt_pos hR hi lo
    · rw [cnt_pos (by omega)]
      have key : ∀ e ∈ Icc lo hi, E (T + R) e lo
          = ∑ m ∈ Icc lo e, cnt (T - 3 ^ e) e m * E R m lo := by
        intro e he
        have hle : e ≤ hi := (mem_Icc.1 he).2
        have hd : 3 ^ e ∣ T := dvd_trans (pow_dvd_pow 3 hle) hT
        have hpos : 3 ^ e ≤ T := Nat.le_of_dvd (Nat.pos_of_ne_zero h0) hd
        have hlt : T - 3 ^ e < T := by have : 0 < 3 ^ e := by positivity
                                       omega
        rw [E, itT (show 3 ^ e ≤ T + R by omega), show T + R - 3 ^ e = (T - 3 ^ e) + R by omega]
        exact ih _ hlt e (Nat.dvd_sub hd dvd_rfl)
      rw [Finset.sum_congr rfl key]
      have rhs : ∀ m ∈ Icc lo hi, cnt T hi m * E R m lo
          = ∑ e ∈ Icc m hi, cnt (T - 3 ^ e) e m * E R m lo := by
        intro m _
        rw [cnt_pos h0, Finset.sum_mul]
        refine Finset.sum_congr rfl (fun e he => ?_)
        have hle : e ≤ hi := (mem_Icc.1 he).2
        have hd : 3 ^ e ∣ T := dvd_trans (pow_dvd_pow 3 hle) hT
        have hpos : 3 ^ e ≤ T := Nat.le_of_dvd (Nat.pos_of_ne_zero h0) hd
        rw [E, itT hpos]
      rw [Finset.sum_congr rfl rhs]
      exact Finset.sum_comm' (fun e m => by simp only [mem_Icc]; omega)

theorem scale (s lo : ℕ) : ∀ X hi, cnt (3 ^ s * X) (hi + s) (lo + s) = cnt X hi lo := by
  intro X
  induction X using Nat.strong_induction_on with
  | _ X ih =>
    intro hi
    by_cases h0 : X = 0
    · subst h0; simp [cnt_zero]
    · have h1 : 3 ^ s * X ≠ 0 := by positivity
      rw [cnt_pos h1, cnt_pos h0, ← map_add_right_Icc, sum_map]
      refine Finset.sum_congr rfl (fun e _ => ?_)
      simp only [addRightEmbedding_apply, E]
      have hiff : 3 ^ (e + s) ≤ 3 ^ s * X ↔ 3 ^ e ≤ X := by
        rw [pow_add, mul_comm (3 ^ e)]
        exact Nat.mul_le_mul_left_iff (by positivity)
      by_cases h : 3 ^ e ≤ X
      · rw [itT (hiff.2 h), itT h]
        have hlt : X - 3 ^ e < X := by have : 0 < 3 ^ e := by positivity
                                       omega
        rw [show 3 ^ s * X - 3 ^ (e + s) = 3 ^ s * (X - 3 ^ e) by
          rw [Nat.mul_sub, pow_add, mul_comm (3 ^ e)]]
        exact ih _ hlt e
      · rw [itF (fun h' => h (hiff.1 h')), itF h]

theorem scaleE (s lo X h : ℕ) : E (3 ^ s * X) (h + s) (lo + s) = E X h lo := by
  unfold E
  have hiff : 3 ^ (h + s) ≤ 3 ^ s * X ↔ 3 ^ h ≤ X := by
    rw [pow_add, mul_comm (3 ^ h)]
    exact Nat.mul_le_mul_left_iff (by positivity)
  by_cases hh : 3 ^ h ≤ X
  · rw [itT (hiff.2 hh), itT hh, show 3 ^ s * X - 3 ^ (h + s) = 3 ^ s * (X - 3 ^ h) by
      rw [Nat.mul_sub, pow_add, mul_comm (3 ^ h)]]
    exact scale s lo _ h
  · rw [itF (fun h' => hh (hiff.1 h')), itF hh]

/-- Split off the block with the largest parts (sum 3^i) from a partition with largest part 3^v. -/
theorem splitE (i v lo R : ℕ) (hv : v ≤ i) (hR : R ≠ 0) :
    E (3 ^ i + R) v lo = ∑ m ∈ Icc lo v, E (3 ^ i) v m * E R m lo := by
  have hp : 3 ^ v ≤ 3 ^ i := Nat.pow_le_pow_right (by norm_num) hv
  rw [E, itT (show 3 ^ v ≤ 3 ^ i + R by omega), show 3 ^ i + R - 3 ^ v = (3 ^ i - 3 ^ v) + R by omega,
    split R hR lo _ v (Nat.dvd_sub (pow_dvd_pow 3 hv) dvd_rfl)]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  have : E (3 ^ i) v m = cnt (3 ^ i - 3 ^ v) v m := by unfold E; exact itT hp _ _
  rw [this]


def N (n k : ℕ) : ℕ := if k ≤ n then E (3 ^ n) (n - k) 0 else 0

theorem N_ne {a b : ℕ} (h : N a b ≠ 0) : b ≤ a := by
  by_contra hb; exact h (by unfold N; exact itF hb _ _)

theorem cnt_one (S : ℕ) : cnt S 0 0 = 1 := by
  induction S using Nat.strong_induction_on with
  | _ S ih =>
    by_cases h0 : S = 0
    · subst h0; exact cnt_zero 0 0
    · rw [cnt_pos h0]
      simp only [Icc_self, sum_singleton, E, pow_zero]
      rw [itT (show 1 ≤ S by omega)]
      exact ih _ (by omega)

/-- E at 3^i with exponents ≥ m, rescaled. -/
theorem E_scale (i h m : ℕ) (hm : m ≤ h) (hi : h ≤ i) :
    E (3 ^ i) h m = E (3 ^ (i - m)) (h - m) 0 := by
  have := scaleE m 0 (3 ^ (i - m)) (h - m)
  rw [← pow_add, show m + (i - m) = i by omega, show h - m + m = h by omega, zero_add] at this
  exact this

theorem N_cube (i j : ℕ) :
    N (i + 1) (j + 1) = ∑ a ∈ range (i + 1), ∑ b ∈ range (i + 1), N i a * N a b * N b j := by
  by_cases hji : j ≤ i
  · have hL : N (i + 1) (j + 1) = ∑ m1 ∈ Icc 0 (i - j), ∑ m2 ∈ Icc 0 m1,
        E (3 ^ i) (i - j) m1 * (E (3 ^ i) m1 m2 * E (3 ^ i) m2 0) := by
      unfold N
      rw [itT (show j + 1 ≤ i + 1 by omega), show i + 1 - (j + 1) = i - j by omega,
        show 3 ^ (i + 1) = 3 ^ i + (3 ^ i + 3 ^ i) by ring,
        splitE i (i - j) 0 _ (by omega) (by positivity)]
      refine Finset.sum_congr rfl (fun m1 hm1 => ?_)
      have hm1' : m1 ≤ i := by simp only [mem_Icc] at hm1; omega
      rw [splitE i m1 0 _ hm1' (by positivity), Finset.mul_sum]
    rw [hL, Finset.sum_sigma', ← Finset.sum_product']
    have hval : ∀ x ∈ (Icc 0 (i - j)).sigma (fun m1 => Icc 0 m1),
        E (3 ^ i) (i - j) x.1 * (E (3 ^ i) x.1 x.2 * E (3 ^ i) x.2 0)
          = N i (i - x.2) * N (i - x.2) (i - x.1) * N (i - x.1) j := by
      intro x hx
      simp only [mem_sigma, mem_Icc] at hx
      obtain ⟨⟨_, hx1⟩, _, hx2⟩ := hx
      unfold N
      rw [itT (show i - x.2 ≤ i by omega), itT (show i - x.1 ≤ i - x.2 by omega),
        itT (show j ≤ i - x.1 by omega), show i - (i - x.2) = x.2 by omega,
        E_scale i (i - j) x.1 (by omega) (by omega), E_scale i x.1 x.2 (by omega) (by omega),
        show i - x.1 - j = i - j - x.1 by omega, show i - x.2 - (i - x.1) = x.1 - x.2 by omega]
      ring
    refine Finset.sum_bij_ne_zero (fun x _ _ => (i - x.2, i - x.1)) ?_ ?_ ?_ ?_
    · intro x hx _
      simp only [mem_sigma, mem_Icc] at hx
      simp only [mem_product, mem_range]; omega
    · rintro ⟨x1, x2⟩ hx _ ⟨y1, y2⟩ hy _ hxy
      simp only [mem_sigma, mem_Icc] at hx hy
      simp only [Prod.mk.injEq] at hxy
      have e1 : x1 = y1 := by omega
      have e2 : x2 = y2 := by omega
      subst e1; subst e2; rfl
    · intro p hp hne
      simp only [mem_product, mem_range] at hp
      have h1 : p.2 ≤ p.1 := N_ne (fun h => hne (by rw [h]; simp))
      have h2 : j ≤ p.2 := N_ne (fun h => hne (by rw [h]; simp))
      have hmem : (⟨i - p.2, i - p.1⟩ : Σ _ : ℕ, ℕ) ∈ (Icc 0 (i - j)).sigma (fun m1 => Icc 0 m1) := by
        simp only [mem_sigma, mem_Icc]; omega
      refine ⟨⟨i - p.2, i - p.1⟩, hmem, ?_, ?_⟩
      · rw [hval _ hmem]
        simp only
        rw [show i - (i - p.1) = p.1 by omega, show i - (i - p.2) = p.2 by omega]
        exact hne
      · exact Prod.ext (by dsimp only; omega) (by dsimp only; omega)
    · intro x hx _
      exact hval x hx
  · have hL : N (i + 1) (j + 1) = 0 := by unfold N; exact itF (by omega) _ _
    rw [hL]; symm
    refine Finset.sum_eq_zero (fun a _ => Finset.sum_eq_zero (fun b hb => ?_))
    simp only [mem_range] at hb
    have : N b j = 0 := by unfold N; exact itF (by omega) _ _
    rw [this, mul_zero]

/-- The defining properties of A078122 (for a lower triangular M, [M^3](i,j) is the finite sum). -/
def IsA078122 (M : ℕ → ℕ → ℤ) : Prop :=
  (∀ i j, i < j → M i j = 0) ∧ (∀ k, M k 0 = 1) ∧ (∀ k, M k k = 1) ∧
    ∀ i j, M (i + 1) (j + 1) = ∑ a ∈ range (i + 1), ∑ b ∈ range (i + 1), M i a * M a b * M b j

theorem N_zero_right (k : ℕ) : N k 0 = 1 := by
  unfold N
  rw [itT (Nat.zero_le k), Nat.sub_zero, E, itT le_rfl, Nat.sub_self, cnt_zero]

theorem N_diag (k : ℕ) : N k k = 1 := by
  unfold N
  rw [itT le_rfl, Nat.sub_self, E, pow_zero, itT (Nat.one_le_pow _ _ (by norm_num)), cnt_one]

theorem N_spec : IsA078122 (fun i j => (N i j : ℤ)) := by
  refine ⟨fun i j h => ?_, fun k => ?_, fun k => ?_, fun i j => ?_⟩
  · have : N i j = 0 := by unfold N; exact itF (by omega) _ _
    simp [this]
  · simp [N_zero_right]
  · simp [N_diag]
  · simp only; rw [N_cube]; push_cast; rfl

theorem eq_N (M : ℕ → ℕ → ℤ) (hM : IsA078122 M) : ∀ i j, M i j = N i j := by
  obtain ⟨hlow, h0, _, hcube⟩ := hM
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro j
    cases j with
    | zero => rw [h0, N_zero_right]; rfl
    | succ j =>
      cases i with
      | zero =>
        rw [hlow 0 (j + 1) (by omega)]
        have : N 0 (j + 1) = 0 := by unfold N; exact itF (by omega) _ _
        simp [this]
      | succ i =>
        rw [hcube, N_cube]
        push_cast
        refine Finset.sum_congr rfl (fun a ha => Finset.sum_congr rfl (fun b hb => ?_))
        simp only [mem_range] at ha hb
        rw [ih i (by omega), ih a (by omega), ih b (by omega)]

/-- A078125: partitions of 3^n into powers of 3 (every power 3^e with e ≤ 3^n allowed). -/
def A078125 (n : ℕ) : ℕ := cnt (3 ^ n) (3 ^ n) 0

theorem cnt_top (S n lo : ℕ) (hS : S < 3 ^ (n + 1)) : ∀ d, cnt S (n + d) lo = cnt S n lo := by
  intro d
  induction d with
  | zero => rfl
  | succ d ih =>
    by_cases h0 : S = 0
    · subst h0; rw [cnt_zero, cnt_zero]
    · rw [← ih, cnt_pos h0, cnt_pos h0]
      by_cases hl : lo ≤ n + d + 1
      · rw [show n + (d + 1) = n + d + 1 by omega, Finset.sum_Icc_succ_top hl]
        have : E S (n + d + 1) lo = 0 := by
          unfold E
          refine itF (fun h => ?_) _ _
          have : 3 ^ (n + 1) ≤ 3 ^ (n + d + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
          omega
        rw [this, add_zero]
      · rw [Finset.Icc_eq_empty (by omega), Finset.Icc_eq_empty (by omega)]

theorem A078125_eq (n : ℕ) : A078125 n = cnt (3 ^ n) n 0 := by
  unfold A078125
  have hn : n ≤ 3 ^ n := (Nat.lt_pow_self (by norm_num)).le
  have := cnt_top (3 ^ n) n 0 (Nat.pow_lt_pow_right (by norm_num) (by omega)) (3 ^ n - n)
  rw [show n + (3 ^ n - n) = 3 ^ n by omega] at this
  exact this

theorem N_rowsum (n : ℕ) : ∑ k ∈ range (n + 1), N n k = A078125 n := by
  rw [A078125_eq, cnt_pos (by positivity), ← Nat.range_succ_eq_Icc_zero,
    ← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  simp only [mem_range] at hk
  unfold N
  rw [itT (show n + 1 - 1 - k ≤ n by omega), show n - (n + 1 - 1 - k) = k by omega]

/-- The conjecture: row sums of A078122 are A078125. -/
theorem A078122_rowsum (M : ℕ → ℕ → ℤ) (hM : IsA078122 M) (n : ℕ) :
    ∑ k ∈ range (n + 1), M n k = A078125 n := by
  rw [Finset.sum_congr rfl (fun k _ => eq_N M hM n k), ← N_rowsum]
  push_cast; rfl

/-- The formula line of the entry: M(n,k) = number of partitions of 3^n into powers of 3 with
largest part 3^(n-k). -/
theorem A078122_formula (M : ℕ → ℕ → ℤ) (hM : IsA078122 M) (n k : ℕ) (hk : k ≤ n) :
    M n k = E (3 ^ n) (n - k) 0 := by
  rw [eq_N M hM]; unfold N; rw [itT hk]
