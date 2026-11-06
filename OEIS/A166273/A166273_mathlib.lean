import Mathlib

/-
OEIS A166273, A166271, A166270, A166269, A166268 (A. Karttunen, 2009):
bisections of the "Jacobi-bridge" heights for m = 12n+7,
  A165605(n) = sum_{i=0..6n+3} J(i, m)   (height at m/2; = A165601(3n+1)),
  A165460(n) = sum_{i=0..4n+2} J(i, m)   (height at m/3),
  A166050(n) = sum_{i=0..2n+1} J(i, m)   (height at m/6).
Conjectures: A166273 = -3 A166269, A166271 = -2 A166269,
A166269 = -(1/2) A166271, A166270 = 2 A166268, A166268 = A166270/2 =
A165605(2n).  In terms of H_x = sum_{0 ≤ i < x m} J(i, m):
  m ≡ 7 (mod 24):  H_{1/3} = 2 H_{1/6},  H_{1/2} = H_{1/6};
  m ≡ 19 (mod 24): H_{1/2} = -3 H_{1/6}, H_{1/3} = -2 H_{1/6}.

Route (`A166273_abstract`): for any χ : ℤ → ℤ that is m-periodic,
completely multiplicative, odd (χ(-1) = -1) with χ(0) = 0, m = 6q + 1,
split (0, m) into six blocks of q integers and each block by residue mod 6
(36 sums `a j r`).  Reflection n ↦ m - n, doubling n ↦ 2n (or 2n - m) and
tripling n ↦ 3n (- m, - 2m) give 66 linear relations (`A166273_refl`,
`A166273_dbl0/1`, `A166273_tpl`) with coefficients χ(2), χ(3); for
(χ(2), χ(3)) = (1, -1) and (-1, -1) they imply the identities (linarith).
For the Jacobi symbol mod m = 12n+7: χ(2) = 1 for n even, -1 for n odd
(m mod 8), and χ(3) = -1 (reciprocity, m ≡ 3 mod 4, m ≡ 1 mod 3).
-/

open Finset

section abstract

variable (χ : ℤ → ℤ) (q : ℕ)

/-- Sum of χ(n) over n = base+1 .. base+len with n % 6 = s. -/
def A166273_W (base len s : ℕ) : ℤ :=
  ∑ l ∈ range len, if (base + l + 1) % 6 = s then χ ((base + l + 1 : ℕ) : ℤ) else 0

theorem A166273_W_add (base L1 L2 s : ℕ) :
    A166273_W χ base (L1 + L2) s = A166273_W χ base L1 s + A166273_W χ (base + L1) L2 s := by
  unfold A166273_W
  rw [sum_range_add]
  congr 1
  refine sum_congr rfl fun i _ => ?_
  rw [show base + (L1 + i) + 1 = base + L1 + i + 1 by omega]

/-- Split a range of length c * L by residue mod c and keep residue e. -/
theorem A166273_split (c e L : ℕ) (he : e < c) (f : ℕ → ℤ)
    (hf : ∀ l, l % c ≠ e → f l = 0) :
    ∑ l ∈ range (c * L), f l = ∑ i ∈ range L, f (c * i + e) := by
  induction L with
  | zero => simp
  | succ L ih =>
    rw [Nat.mul_succ, sum_range_add, ih, sum_range_succ]
    congr 1
    rw [sum_eq_single e]
    · intro b hb hbe
      apply hf
      rw [mem_range] at hb
      rw [Nat.add_comm, Nat.add_mul_mod_self_left]
      rw [Nat.mod_eq_of_lt hb]; exact hbe
    · intro h; exact absurd (mem_range.mpr he) h


variable {χ q}

theorem A166273_ite_pos {α : Type*} {p : Prop} [Decidable p] (h : p) {a b : α} :
    (if p then a else b) = a := by simp [h]

theorem A166273_ite_neg {α : Type*} {p : Prop} [Decidable p] (h : ¬ p) {a b : α} :
    (if p then a else b) = b := by simp [h]

/-- The 6 residue classes of a window add up to the plain sum. -/
theorem A166273_W_sum6 (base len : ℕ) :
    ∑ r ∈ range 6, A166273_W χ base len r = ∑ l ∈ range len, χ ((base + l + 1 : ℕ) : ℤ) := by
  unfold A166273_W
  rw [sum_comm]
  refine sum_congr rfl fun l _ => ?_
  rw [sum_ite_eq]
  simp [Nat.mod_lt _ (by norm_num : 6 > 0)]

section rel
variable (hper : ∀ a : ℤ, χ (a + (6 * q + 1 : ℕ)) = χ a)
  (hmul : ∀ a b : ℤ, χ (a * b) = χ a * χ b) (hneg : χ (-1) = -1)
include hper hmul hneg

theorem A166273_refl (j r : ℕ) (hj : j ≤ 5) (hr : r < 6) :
    A166273_W χ ((5 - j) * q) q ((7 - r) % 6) = - A166273_W χ (j * q) q r := by
  unfold A166273_W
  rw [← sum_range_reflect, ← sum_neg_distrib]
  refine sum_congr rfl fun i hi => ?_
  rw [mem_range] at hi
  have hc : ((5 - j) * q + (q - 1 - i) + 1) % 6 = (7 - r) % 6 ↔ (j * q + i + 1) % 6 = r := by
    interval_cases j <;> omega
  have hv : χ (((5 - j) * q + (q - 1 - i) + 1 : ℕ) : ℤ) = - χ ((j * q + i + 1 : ℕ) : ℤ) := by
    have e : (((5 - j) * q + (q - 1 - i) + 1 : ℕ) : ℤ) =
        (-1) * ((j * q + i + 1 : ℕ) : ℤ) + ((6 * q + 1 : ℕ) : ℤ) := by
      interval_cases j <;> push_cast <;> omega
    rw [e, hper, hmul, hneg]; ring
  by_cases h : (j * q + i + 1) % 6 = r
  · rw [A166273_ite_pos (hc.mpr h), A166273_ite_pos h, hv]
  · rw [A166273_ite_neg (fun h' => h (hc.mp h')), A166273_ite_neg h, neg_zero]

omit hmul hneg in
theorem A166273_perk (t : ℕ) (a : ℤ) : χ (a + (t : ℤ) * ((6 * q + 1 : ℕ) : ℤ)) = χ a := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [show a + ((t + 1 : ℕ) : ℤ) * ((6 * q + 1 : ℕ) : ℤ) =
      (a + (t : ℤ) * ((6 * q + 1 : ℕ) : ℤ)) + ((6 * q + 1 : ℕ) : ℤ) by push_cast; ring, hper, ih]

omit hper hneg in
theorem A166273_dbl0 (j r : ℕ) (hj : j ≤ 2) (hr : r < 3) :
    χ 2 * (A166273_W χ (j * q) q r + A166273_W χ (j * q) q (r + 3)) =
      A166273_W χ (2 * j * q) q (2 * r) + A166273_W χ ((2 * j + 1) * q) q (2 * r) := by
  have e1 : (2 * j + 1) * q = 2 * j * q + q := by ring
  rw [e1, ← A166273_W_add, ← two_mul]
  unfold A166273_W
  rw [A166273_split 2 1 q (by norm_num)]
  · rw [← sum_add_distrib, mul_sum]
    refine sum_congr rfl fun i _ => ?_
    have hv : χ ((2 * j * q + (2 * i + 1) + 1 : ℕ) : ℤ) = χ 2 * χ ((j * q + i + 1 : ℕ) : ℤ) := by
      rw [← hmul]; congr 1; push_cast; ring
    rw [hv]
    by_cases h1 : (j * q + i + 1) % 6 = r
    · have h3 : (2 * j * q + (2 * i + 1) + 1) % 6 = 2 * r := by interval_cases j <;> omega
      rw [A166273_ite_pos h1, A166273_ite_neg (by omega), A166273_ite_pos h3]; ring
    · by_cases h2 : (j * q + i + 1) % 6 = r + 3
      · have h3 : (2 * j * q + (2 * i + 1) + 1) % 6 = 2 * r := by interval_cases j <;> omega
        rw [A166273_ite_neg h1, A166273_ite_pos h2, A166273_ite_pos h3]; ring
      · have h3 : ¬ (2 * j * q + (2 * i + 1) + 1) % 6 = 2 * r := by interval_cases j <;> omega
        rw [A166273_ite_neg h1, A166273_ite_neg h2, A166273_ite_neg h3]; ring
  · intro l hl
    have : ¬ (2 * j * q + l + 1) % 6 = 2 * r := by interval_cases j <;> omega
    rw [A166273_ite_neg this]

omit hneg in
theorem A166273_dbl1 (j r : ℕ) (hj1 : 3 ≤ j) (hj : j ≤ 5) (hr : r < 3) :
    χ 2 * (A166273_W χ (j * q) q r + A166273_W χ (j * q) q (r + 3)) =
      A166273_W χ ((2 * j - 6) * q) q ((2 * r + 5) % 6) +
        A166273_W χ ((2 * j - 5) * q) q ((2 * r + 5) % 6) := by
  have e1 : (2 * j - 5) * q = (2 * j - 6) * q + q := by interval_cases j <;> ring_nf
  rw [e1, ← A166273_W_add, ← two_mul]
  unfold A166273_W
  rw [A166273_split 2 0 q (by norm_num)]
  · rw [← sum_add_distrib, mul_sum]
    refine sum_congr rfl fun i _ => ?_
    have hv : χ (((2 * j - 6) * q + (2 * i + 0) + 1 : ℕ) : ℤ) = χ 2 * χ ((j * q + i + 1 : ℕ) : ℤ) := by
      rw [← hmul, ← hper]; congr 1; interval_cases j <;> push_cast <;> ring_nf
    rw [hv]
    by_cases h1 : (j * q + i + 1) % 6 = r
    · have h3 : ((2 * j - 6) * q + (2 * i + 0) + 1) % 6 = (2 * r + 5) % 6 := by
        interval_cases j <;> omega
      rw [A166273_ite_pos h1, A166273_ite_neg (by omega), A166273_ite_pos h3]; ring
    · by_cases h2 : (j * q + i + 1) % 6 = r + 3
      · have h3 : ((2 * j - 6) * q + (2 * i + 0) + 1) % 6 = (2 * r + 5) % 6 := by
          interval_cases j <;> omega
        rw [A166273_ite_neg h1, A166273_ite_pos h2, A166273_ite_pos h3]; ring
      · have h3 : ¬ ((2 * j - 6) * q + (2 * i + 0) + 1) % 6 = (2 * r + 5) % 6 := by
          interval_cases j <;> omega
        rw [A166273_ite_neg h1, A166273_ite_neg h2, A166273_ite_neg h3]; ring
  · intro l hl
    have : ¬ ((2 * j - 6) * q + l + 1) % 6 = (2 * r + 5) % 6 := by interval_cases j <;> omega
    rw [A166273_ite_neg this]

omit hneg in
theorem A166273_tpl (t j r : ℕ) (ht : t ≤ 2) (hj1 : 2 * t ≤ j) (hj : j ≤ 2 * t + 1) (hr : r < 2) :
    χ 3 * (A166273_W χ (j * q) q r + A166273_W χ (j * q) q (r + 2) +
        A166273_W χ (j * q) q (r + 4)) =
      A166273_W χ ((3 * j - 6 * t) * q) q ((3 * r + 6 - t) % 6) +
        A166273_W χ ((3 * j - 6 * t + 1) * q) q ((3 * r + 6 - t) % 6) +
        A166273_W χ ((3 * j - 6 * t + 2) * q) q ((3 * r + 6 - t) % 6) := by
  have e1 : (3 * j - 6 * t + 1) * q = (3 * j - 6 * t) * q + q := by ring
  have e2 : (3 * j - 6 * t + 2) * q = (3 * j - 6 * t) * q + (q + q) := by ring
  rw [e1, e2, ← A166273_W_add χ ((3 * j - 6 * t) * q) q q,
    ← A166273_W_add χ ((3 * j - 6 * t) * q) (q + q) q, show q + q + q = 3 * q by ring]
  unfold A166273_W
  rw [A166273_split 3 (2 - t) q (by omega)]
  · rw [← sum_add_distrib, ← sum_add_distrib, mul_sum]
    refine sum_congr rfl fun i _ => ?_
    have hv : χ (((3 * j - 6 * t) * q + (3 * i + (2 - t)) + 1 : ℕ) : ℤ) =
        χ 3 * χ ((j * q + i + 1 : ℕ) : ℤ) := by
      have hN : 3 * (j * q + i + 1) = ((3 * j - 6 * t) * q + (3 * i + (2 - t)) + 1) + t * (6 * q + 1) := by
        interval_cases t <;> interval_cases j <;> omega
      have hZ : (3 : ℤ) * ((j * q + i + 1 : ℕ) : ℤ) =
          (((3 * j - 6 * t) * q + (3 * i + (2 - t)) + 1 : ℕ) : ℤ) + (t : ℤ) * ((6 * q + 1 : ℕ) : ℤ) := by
        exact_mod_cast hN
      rw [← hmul, hZ, A166273_perk hper]
    rw [hv]
    have key : ((3 * j - 6 * t) * q + (3 * i + (2 - t)) + 1) % 6 = (3 * r + 6 - t) % 6 ↔
        (j * q + i + 1) % 2 = r := by
      interval_cases t <;> interval_cases j <;> omega
    by_cases h0 : (j * q + i + 1) % 2 = r
    · rw [A166273_ite_pos (key.mpr h0)]
      rcases (by omega : (j * q + i + 1) % 6 = r ∨ (j * q + i + 1) % 6 = r + 2 ∨
          (j * q + i + 1) % 6 = r + 4) with h | h | h
      · rw [A166273_ite_pos h, A166273_ite_neg (by omega), A166273_ite_neg (by omega)]; ring
      · rw [A166273_ite_neg (by omega), A166273_ite_pos h, A166273_ite_neg (by omega)]; ring
      · rw [A166273_ite_neg (by omega), A166273_ite_neg (by omega), A166273_ite_pos h]; ring
    · rw [A166273_ite_neg (fun h' => h0 (key.mp h')), A166273_ite_neg (by omega), A166273_ite_neg (by omega),
        A166273_ite_neg (by omega)]; ring
  · intro l hl
    have : ¬ ((3 * j - 6 * t) * q + l + 1) % 6 = (3 * r + 6 - t) % 6 := by
      interval_cases t <;> interval_cases j <;> omega
    rw [A166273_ite_neg this]

end rel

theorem A166273_S (k : ℕ) : ∑ l ∈ range (k * q), χ ((l + 1 : ℕ) : ℤ) =
    ∑ j ∈ range k, ∑ r ∈ range 6, A166273_W χ (j * q) q r := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.succ_mul, sum_range_add, ih, sum_range_succ, A166273_W_sum6]

/-- The identities for an abstract odd character, m = 6q + 1. -/
theorem A166273_abstract
    (hper : ∀ a : ℤ, χ (a + (6 * q + 1 : ℕ)) = χ a)
    (hmul : ∀ a b : ℤ, χ (a * b) = χ a * χ b) (hneg : χ (-1) = -1) (h3 : χ 3 = -1) :
    (χ 2 = 1 →
      ∑ l ∈ range (2 * q), χ ((l + 1 : ℕ) : ℤ) = 2 * ∑ l ∈ range (1 * q), χ ((l + 1 : ℕ) : ℤ) ∧
      ∑ l ∈ range (1 * q), χ ((l + 1 : ℕ) : ℤ) = ∑ l ∈ range (3 * q), χ ((l + 1 : ℕ) : ℤ)) ∧
    (χ 2 = -1 →
      ∑ l ∈ range (3 * q), χ ((l + 1 : ℕ) : ℤ) = -3 * ∑ l ∈ range (1 * q), χ ((l + 1 : ℕ) : ℤ) ∧
      ∑ l ∈ range (2 * q), χ ((l + 1 : ℕ) : ℤ) = -2 * ∑ l ∈ range (1 * q), χ ((l + 1 : ℕ) : ℤ)) := by
  have r00 := A166273_refl hper hmul hneg 0 0 (by norm_num) (by norm_num)
  have r01 := A166273_refl hper hmul hneg 0 1 (by norm_num) (by norm_num)
  have r02 := A166273_refl hper hmul hneg 0 2 (by norm_num) (by norm_num)
  have r03 := A166273_refl hper hmul hneg 0 3 (by norm_num) (by norm_num)
  have r04 := A166273_refl hper hmul hneg 0 4 (by norm_num) (by norm_num)
  have r05 := A166273_refl hper hmul hneg 0 5 (by norm_num) (by norm_num)
  have r10 := A166273_refl hper hmul hneg 1 0 (by norm_num) (by norm_num)
  have r11 := A166273_refl hper hmul hneg 1 1 (by norm_num) (by norm_num)
  have r12 := A166273_refl hper hmul hneg 1 2 (by norm_num) (by norm_num)
  have r13 := A166273_refl hper hmul hneg 1 3 (by norm_num) (by norm_num)
  have r14 := A166273_refl hper hmul hneg 1 4 (by norm_num) (by norm_num)
  have r15 := A166273_refl hper hmul hneg 1 5 (by norm_num) (by norm_num)
  have r20 := A166273_refl hper hmul hneg 2 0 (by norm_num) (by norm_num)
  have r21 := A166273_refl hper hmul hneg 2 1 (by norm_num) (by norm_num)
  have r22 := A166273_refl hper hmul hneg 2 2 (by norm_num) (by norm_num)
  have r23 := A166273_refl hper hmul hneg 2 3 (by norm_num) (by norm_num)
  have r24 := A166273_refl hper hmul hneg 2 4 (by norm_num) (by norm_num)
  have r25 := A166273_refl hper hmul hneg 2 5 (by norm_num) (by norm_num)
  have r30 := A166273_refl hper hmul hneg 3 0 (by norm_num) (by norm_num)
  have r31 := A166273_refl hper hmul hneg 3 1 (by norm_num) (by norm_num)
  have r32 := A166273_refl hper hmul hneg 3 2 (by norm_num) (by norm_num)
  have r33 := A166273_refl hper hmul hneg 3 3 (by norm_num) (by norm_num)
  have r34 := A166273_refl hper hmul hneg 3 4 (by norm_num) (by norm_num)
  have r35 := A166273_refl hper hmul hneg 3 5 (by norm_num) (by norm_num)
  have r40 := A166273_refl hper hmul hneg 4 0 (by norm_num) (by norm_num)
  have r41 := A166273_refl hper hmul hneg 4 1 (by norm_num) (by norm_num)
  have r42 := A166273_refl hper hmul hneg 4 2 (by norm_num) (by norm_num)
  have r43 := A166273_refl hper hmul hneg 4 3 (by norm_num) (by norm_num)
  have r44 := A166273_refl hper hmul hneg 4 4 (by norm_num) (by norm_num)
  have r45 := A166273_refl hper hmul hneg 4 5 (by norm_num) (by norm_num)
  have r50 := A166273_refl hper hmul hneg 5 0 (by norm_num) (by norm_num)
  have r51 := A166273_refl hper hmul hneg 5 1 (by norm_num) (by norm_num)
  have r52 := A166273_refl hper hmul hneg 5 2 (by norm_num) (by norm_num)
  have r53 := A166273_refl hper hmul hneg 5 3 (by norm_num) (by norm_num)
  have r54 := A166273_refl hper hmul hneg 5 4 (by norm_num) (by norm_num)
  have r55 := A166273_refl hper hmul hneg 5 5 (by norm_num) (by norm_num)
  have d00 := A166273_dbl0 hmul (q := q) 0 0 (by norm_num) (by norm_num)
  have d01 := A166273_dbl0 hmul (q := q) 0 1 (by norm_num) (by norm_num)
  have d02 := A166273_dbl0 hmul (q := q) 0 2 (by norm_num) (by norm_num)
  have d10 := A166273_dbl0 hmul (q := q) 1 0 (by norm_num) (by norm_num)
  have d11 := A166273_dbl0 hmul (q := q) 1 1 (by norm_num) (by norm_num)
  have d12 := A166273_dbl0 hmul (q := q) 1 2 (by norm_num) (by norm_num)
  have d20 := A166273_dbl0 hmul (q := q) 2 0 (by norm_num) (by norm_num)
  have d21 := A166273_dbl0 hmul (q := q) 2 1 (by norm_num) (by norm_num)
  have d22 := A166273_dbl0 hmul (q := q) 2 2 (by norm_num) (by norm_num)
  have d30 := A166273_dbl1 hper hmul 3 0 (by norm_num) (by norm_num) (by norm_num)
  have d31 := A166273_dbl1 hper hmul 3 1 (by norm_num) (by norm_num) (by norm_num)
  have d32 := A166273_dbl1 hper hmul 3 2 (by norm_num) (by norm_num) (by norm_num)
  have d40 := A166273_dbl1 hper hmul 4 0 (by norm_num) (by norm_num) (by norm_num)
  have d41 := A166273_dbl1 hper hmul 4 1 (by norm_num) (by norm_num) (by norm_num)
  have d42 := A166273_dbl1 hper hmul 4 2 (by norm_num) (by norm_num) (by norm_num)
  have d50 := A166273_dbl1 hper hmul 5 0 (by norm_num) (by norm_num) (by norm_num)
  have d51 := A166273_dbl1 hper hmul 5 1 (by norm_num) (by norm_num) (by norm_num)
  have d52 := A166273_dbl1 hper hmul 5 2 (by norm_num) (by norm_num) (by norm_num)
  have t00 := A166273_tpl hper hmul 0 0 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t01 := A166273_tpl hper hmul 0 0 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t10 := A166273_tpl hper hmul 0 1 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t11 := A166273_tpl hper hmul 0 1 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t20 := A166273_tpl hper hmul 1 2 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t21 := A166273_tpl hper hmul 1 2 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t30 := A166273_tpl hper hmul 1 3 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t31 := A166273_tpl hper hmul 1 3 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t40 := A166273_tpl hper hmul 2 4 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t41 := A166273_tpl hper hmul 2 4 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t50 := A166273_tpl hper hmul 2 5 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t51 := A166273_tpl hper hmul 2 5 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [A166273_S, A166273_S, A166273_S]
  simp only [sum_range_succ, sum_range_zero, zero_add] at *
  rw [h3] at *
  clear hper hmul hneg
  norm_num at *
  constructor
  · intro h2
    simp only [h2, one_mul] at d00 d01 d02 d10 d11 d12 d20 d21 d22 d30 d31 d32 d40 d41 d42 d50 d51 d52
    constructor <;> linarith
  · intro h2
    simp only [h2, neg_one_mul, neg_add] at d00 d01 d02 d10 d11 d12 d20 d21 d22 d30 d31 d32 d40 d41 d42 d50 d51 d52
    constructor <;> linarith

/-! ### The OEIS sequences (Jacobi symbol `J(a | b) = jacobiSym a b`) -/

/-- A165601(n) = sum_{i=0..2n+1} J(i, 4n+3). -/
def A165601 (n : ℕ) : ℤ := ∑ i ∈ range (2 * n + 2), jacobiSym (i : ℤ) (4 * n + 3)
/-- A165605(n) = A165601(3n+1). -/
def A165605 (n : ℕ) : ℤ := A165601 (3 * n + 1)
/-- A165460(n) = sum_{i=0..4n+2} J(i, 12n+7). -/
def A165460 (n : ℕ) : ℤ := ∑ i ∈ range (4 * n + 3), jacobiSym (i : ℤ) (12 * n + 7)
/-- A166050(n) = sum_{i=0..2n+1} J(i, 12n+7). -/
def A166050 (n : ℕ) : ℤ := ∑ i ∈ range (2 * n + 2), jacobiSym (i : ℤ) (12 * n + 7)
def A166273 (n : ℕ) : ℤ := A165605 (2 * n + 1)
def A166271 (n : ℕ) : ℤ := A165460 (2 * n + 1)
def A166270 (n : ℕ) : ℤ := A165460 (2 * n)
def A166269 (n : ℕ) : ℤ := A166050 (2 * n + 1)
def A166268 (n : ℕ) : ℤ := A166050 (2 * n)

theorem A166273_jacobi (n : ℕ) :
    (n % 2 = 0 → A165460 n = 2 * A166050 n ∧ A166050 n = A165605 n) ∧
    (n % 2 = 1 → A165605 n = -3 * A166050 n ∧ A165460 n = -2 * A166050 n) := by
  set m := 12 * n + 7 with hm
  set q := 2 * n + 1 with hq
  have hmq : m = 6 * q + 1 := by omega
  have hodd : Odd m := ⟨6 * n + 3, by omega⟩
  set χ : ℤ → ℤ := fun a => jacobiSym a m with hχ
  have hper : ∀ a : ℤ, χ (a + (6 * q + 1 : ℕ)) = χ a := by
    intro a
    simp only [hχ, ← hmq]
    exact jacobiSym.mod_left' (by simp)
  have hmul : ∀ a b : ℤ, χ (a * b) = χ a * χ b := fun a b => jacobiSym.mul_left a b m
  have hneg : χ (-1) = -1 := by
    simp only [hχ]
    rw [jacobiSym.at_neg_one hodd, ZMod.χ₄_nat_three_mod_four (by omega)]
  have h3 : χ 3 = -1 := by
    simp only [hχ]
    have := jacobiSym.quadratic_reciprocity_three_mod_four (a := 3) (b := m) (by norm_num)
      (by omega)
    push_cast at this
    rw [this, jacobiSym.mod_left, show ((m : ℤ) % ((3 : ℕ) : ℤ)) = 1 by push_cast; omega,
      jacobiSym.one_left]
  have h2 : χ 2 = if n % 2 = 0 then 1 else -1 := by
    simp only [hχ]
    rw [jacobiSym.at_two hodd, ZMod.χ₈_nat_eq_if_mod_eight m]
    rw [A166273_ite_neg (show ¬ m % 2 = 0 by omega)]
    rcases Nat.mod_two_eq_zero_or_one n with h | h
    · rw [A166273_ite_pos (show m % 8 = 1 ∨ m % 8 = 7 by omega), A166273_ite_pos h]
    · rw [A166273_ite_neg (show ¬ (m % 8 = 1 ∨ m % 8 = 7) by omega), A166273_ite_neg (by omega)]
  have h0 : χ 0 = 0 := by simp only [hχ]; exact jacobiSym.zero_left (by omega)
  have hS : ∀ k, ∑ i ∈ range (k * q + 1), χ (i : ℤ) = ∑ l ∈ range (k * q), χ ((l + 1 : ℕ) : ℤ) := by
    intro k
    rw [sum_range_succ']
    simp [h0]
  have e6 : A166050 n = ∑ i ∈ range (1 * q + 1), χ (i : ℤ) := by
    simp only [A166050, hχ, hm]; rw [show 2 * n + 2 = 1 * q + 1 by omega]
  have e3 : A165460 n = ∑ i ∈ range (2 * q + 1), χ (i : ℤ) := by
    simp only [A165460, hχ, hm]; rw [show 4 * n + 3 = 2 * q + 1 by omega]
  have e2 : A165605 n = ∑ i ∈ range (3 * q + 1), χ (i : ℤ) := by
    simp only [A165605, A165601, hχ, hm]
    rw [show 2 * (3 * n + 1) + 2 = 3 * q + 1 by omega, show 4 * (3 * n + 1) + 3 = 12 * n + 7 by omega]
  rw [e6, e3, e2, hS, hS, hS]
  have ab := A166273_abstract hper hmul hneg h3
  constructor
  · intro hn
    have := ab.1 (by rw [h2, A166273_ite_pos hn])
    constructor <;> linarith [this.1, this.2]
  · intro hn
    have := ab.2 (by rw [h2, A166273_ite_neg (by omega)])
    constructor <;> linarith [this.1, this.2]

/-- A166273: a(n) = -3 A166269(n). -/
theorem A166273_main (n : ℕ) : A166273 n = -3 * A166269 n :=
  ((A166273_jacobi (2 * n + 1)).2 (by omega)).1

/-- A166271: a(n) = -2 A166269(n). -/
theorem A166271_main (n : ℕ) : A166271 n = -2 * A166269 n :=
  ((A166273_jacobi (2 * n + 1)).2 (by omega)).2

/-- A166269: a(n) = -(1/2) A166271(n). -/
theorem A166269_main (n : ℕ) : 2 * A166269 n = - A166271 n := by
  rw [A166271_main]; ring

/-- A166270: a(n) = 2 A166268(n). -/
theorem A166270_main (n : ℕ) : A166270 n = 2 * A166268 n :=
  ((A166273_jacobi (2 * n)).1 (by omega)).1

/-- A166268: a(n) = A166270(n)/2 and a(n) = A165605(2n). -/
theorem A166268_main (n : ℕ) : 2 * A166268 n = A166270 n ∧ A166268 n = A165605 (2 * n) :=
  ⟨by rw [A166270_main], ((A166273_jacobi (2 * n)).1 (by omega)).2⟩

/-- First terms of A166273 and A166269 as listed in the OEIS. -/
theorem A166273_data : (List.range 6).map A166273 = [3, 3, 3, 6, 6, 9] ∧
    (List.range 6).map A166269 = [-1, -1, -1, -2, -2, -3] := by
  decide +kernel
