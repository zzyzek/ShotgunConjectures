/-
OEIS A124431, Mathlib proof of R. J. Mathar's conjectured recurrence.

a(n) = Σ_{k=0..n} 2^k C(⌊(n+k)/2⌋, k) C(⌊(n+k+1)/2⌋, k)  (`A124431_a`, ℕ, as in the entry).

Main theorem `A124431_conjecture`: for every n ≥ 4,
  (n+1) a(n) - 2(2n+1) a(n-1) + 2(n-1) a(n-2) + 2(5-2n) a(n-3) + (n-3) a(n-4) = 0  (in ℤ).
`A124431_data`: a(0..11) = 1, 3, 9, 29, 97, 331, 1145, 4001, 14089, 49915, 177713, 635293.

Proof (creative telescoping).
* Reindexing (`A124431_w_eq`, `A124431_a_eq_A`): grouping the summands k = n - 2i and
  k = n + 1 - 2i gives a(n) = Σ_{i=0}^{n+1} w(n, i) with
  w(n, i) = 2^(n-2i) (C(n-i, i)^2 + 2 C(n-i, i-1) C(n-i+1, i)), a single hypergeometric term
  in (n, i) without floors. `A124431_Cz` is the binomial coefficient on ℤ × ℤ (0 off 0 ≤ y ≤ x).
* Certificate (`A124431_G`): G(n, i) = 2^(n-2i) Σ (u + v i) C(n-i-a, i-b) C(n-i-a', i-b')
  (12 terms, found by linear algebra, see certificate/). `A124431_core` is the identity
  Σ_l c_l(n) w(n-l, i) = G(n, i+1) - G(n, i) whenever (n-i+1)(n-i)(n-i-1)(n-i-2)(n-i-3) ≠ 0.
  Its proof expresses every binomial C(n-i+1-α, i+β) through E = C(n-i+1, i) with the
  contiguous relations `A124431_R1`..`A124431_R3` (valid on all of ℤ × ℤ) and reduces to the
  rational-function identity `A124431_rat` (field_simp; ring).
* For n ≥ 8 every i < n + 2 is covered by `A124431_core` (i ≤ n - 4) or all terms vanish
  (2i ≥ n + 2); summing over i telescopes to G(n, n+2) - G(n, 0) = 0 (`A124431_A_rec`).
  n = 4..7 are checked by `decide` (`A124431_small`).

Not checked in Lean: nothing for the statement above. The generator scripts in certificate/
(which produced `A124431_G`, `A124431_rat` and `A124431_core`) are outside Lean but their output
is checked here.
-/
import Mathlib


/-- Binomial coefficient on ℤ × ℤ: C(x, y) for 0 ≤ y ≤ x, else 0. -/
def A124431_Cz (x y : ℤ) : ℚ := if 0 ≤ y ∧ y ≤ x then ((x.toNat.choose y.toNat : ℕ) : ℚ) else 0

theorem A124431_Cz_nat (p q : ℕ) : A124431_Cz p q = (p.choose q : ℚ) := by
  unfold A124431_Cz
  by_cases h : q ≤ p
  · rw [ite_eq_left ⟨by positivity, by exact_mod_cast h⟩]
    simp
  · rw [ite_eq_right (by omega), Nat.choose_eq_zero_of_lt (by omega)]
    simp

theorem A124431_Cz_negl {x y : ℤ} (h : x < 0) : A124431_Cz x y = 0 := by
  unfold A124431_Cz
  rw [ite_eq_right (by omega)]

theorem A124431_Cz_negr {x y : ℤ} (h : y < 0) : A124431_Cz x y = 0 := by
  unfold A124431_Cz
  rw [ite_eq_right (by omega)]

theorem A124431_Cz_lt {x y : ℤ} (h : x < y) : A124431_Cz x y = 0 := by
  unfold A124431_Cz
  rw [ite_eq_right (by omega)]

/-- C(x-1, y) x = C(x, y) (x - y). -/
theorem A124431_R1 (x y : ℤ) : A124431_Cz (x - 1) y * x = A124431_Cz x y * (x - y) := by
  rcases lt_or_ge y 0 with hy | hy
  · rw [A124431_Cz_negr hy, A124431_Cz_negr hy]; ring
  rcases lt_or_ge x 1 with hx | hx
  · rw [A124431_Cz_negl (by omega)]
    rcases lt_or_ge x y with hxy | hxy
    · rw [A124431_Cz_lt hxy]; ring
    · have : x = y := by omega
      subst this; ring
  obtain ⟨q, rfl⟩ := Int.eq_ofNat_of_zero_le hy
  obtain ⟨p, rfl⟩ : ∃ p : ℕ, x = ((p + 1 : ℕ) : ℤ) := ⟨(x - 1).toNat, by omega⟩
  rw [show ((p + 1 : ℕ) : ℤ) - 1 = (p : ℤ) by push_cast; ring, A124431_Cz_nat, A124431_Cz_nat]
  have h := Nat.choose_mul_succ_eq p q
  by_cases hq : q ≤ p + 1
  · have h' : ((p.choose q : ℕ) : ℚ) * ((p + 1 : ℕ) : ℚ) = (((p + 1).choose q : ℕ) : ℚ) * ((p + 1 - q : ℕ) : ℚ) := by
      exact_mod_cast h
    rw [Nat.cast_sub hq] at h'
    push_cast at h' ⊢
    linear_combination h'
  · rw [Nat.choose_eq_zero_of_lt (by omega), Nat.choose_eq_zero_of_lt (by omega)]
    simp

/-- C(x-1, y-1) x = C(x, y) y. -/
theorem A124431_R2 (x y : ℤ) : A124431_Cz (x - 1) (y - 1) * x = A124431_Cz x y * y := by
  rcases lt_or_ge y 1 with hy | hy
  · rw [A124431_Cz_negr (by omega : y - 1 < 0)]
    rcases lt_or_ge y 0 with hy0 | hy0
    · rw [A124431_Cz_negr hy0]; ring
    · have : y = 0 := by omega
      subst this; ring
  rcases lt_or_ge x 1 with hx | hx
  · rw [A124431_Cz_negl (by omega), A124431_Cz_lt (by omega)]; ring
  obtain ⟨q, rfl⟩ : ∃ q : ℕ, y = ((q + 1 : ℕ) : ℤ) := ⟨(y - 1).toNat, by omega⟩
  obtain ⟨p, rfl⟩ : ∃ p : ℕ, x = ((p + 1 : ℕ) : ℤ) := ⟨(x - 1).toNat, by omega⟩
  rw [show ((p + 1 : ℕ) : ℤ) - 1 = (p : ℤ) by push_cast; ring,
    show ((q + 1 : ℕ) : ℤ) - 1 = (q : ℤ) by push_cast; ring, A124431_Cz_nat, A124431_Cz_nat]
  have h : (((p + 1 : ℕ) : ℚ)) * ((p.choose q : ℕ) : ℚ) = (((p + 1).choose (q + 1) : ℕ) : ℚ) * ((q + 1 : ℕ) : ℚ) := by
    exact_mod_cast Nat.add_one_mul_choose_eq p q
  push_cast at h ⊢
  linear_combination h

/-- C(x, y+1) (y+1) = C(x, y) (x - y). -/
theorem A124431_R3 (x y : ℤ) : A124431_Cz x (y + 1) * (y + 1) = A124431_Cz x y * (x - y) := by
  rcases lt_or_ge y 0 with hy | hy
  · rw [A124431_Cz_negr hy]
    rcases lt_or_ge (y + 1) 0 with hy1 | hy1
    · rw [A124431_Cz_negr hy1]; ring
    · have h1 : y + 1 = 0 := by omega
      have h2 : (y : ℚ) + 1 = 0 := by exact_mod_cast h1
      rw [h2]; ring
  rcases lt_or_ge x 0 with hx | hx
  · rw [A124431_Cz_negl hx, A124431_Cz_negl hx]; ring
  obtain ⟨q, rfl⟩ := Int.eq_ofNat_of_zero_le hy
  obtain ⟨p, rfl⟩ := Int.eq_ofNat_of_zero_le hx
  rw [show (q : ℤ) + 1 = ((q + 1 : ℕ) : ℤ) by push_cast; ring, A124431_Cz_nat, A124431_Cz_nat]
  by_cases hq : q ≤ p
  · have h : ((p.choose (q + 1) : ℕ) : ℚ) * ((q + 1 : ℕ) : ℚ) = ((p.choose q : ℕ) : ℚ) * ((p - q : ℕ) : ℚ) := by
      exact_mod_cast Nat.choose_succ_right_eq p q
    rw [Nat.cast_sub hq] at h
    push_cast at h ⊢
    linear_combination h
  · rw [Nat.choose_eq_zero_of_lt (by omega), Nat.choose_eq_zero_of_lt (by omega)]
    simp

/-- The summand w(m, i) = 2^(m-2i) (C(m-i, i)^2 + 2 C(m-i, i-1) C(m-i+1, i)). -/
noncomputable def A124431_w (m i : ℤ) : ℚ :=
  2 ^ (m - 2 * i) * (A124431_Cz (m - i) i ^ 2 + 2 * A124431_Cz (m - i) (i - 1) * A124431_Cz (m - i + 1) i)

/-- The telescoping certificate G(n, i). -/
noncomputable def A124431_G (n i : ℤ) : ℚ :=
  2 ^ (n - 2 * i) * (((1 : ℚ) + (4 : ℚ) * i) * A124431_Cz (n - i) (i) * A124431_Cz (n - i) (i) +
    ((0 : ℚ) + (-6 : ℚ) * i) * A124431_Cz (n - i) (i) * A124431_Cz (n - i) (i - 1) +
    ((0 : ℚ) + (-4 : ℚ) * i) * A124431_Cz (n - i) (i - 1) * A124431_Cz (n - i) (i - 1) +
    ((-2 : ℚ) + (-5 : ℚ) * i) * A124431_Cz (n - i) (i) * A124431_Cz (n - i - 1) (i) +
    ((-1/2 : ℚ) + (0 : ℚ) * i) * A124431_Cz (n - i) (i) * A124431_Cz (n - i - 2) (i) +
    ((1/2 : ℚ) + (-1/4 : ℚ) * i) * A124431_Cz (n - i) (i) * A124431_Cz (n - i - 3) (i) +
    ((1 : ℚ) + (0 : ℚ) * i) * A124431_Cz (n - i - 1) (i) * A124431_Cz (n - i - 1) (i) +
    ((0 : ℚ) + (3/4 : ℚ) * i) * A124431_Cz (n - i - 1) (i) * A124431_Cz (n - i - 2) (i) +
    ((0 : ℚ) + (-1/2 : ℚ) * i) * A124431_Cz (n - i - 1) (i) * A124431_Cz (n - i - 3) (i) +
    ((1/4 : ℚ) + (2 : ℚ) * i) * A124431_Cz (n - i - 2) (i) * A124431_Cz (n - i - 2) (i) +
    ((0 : ℚ) + (-5/4 : ℚ) * i) * A124431_Cz (n - i - 2) (i) * A124431_Cz (n - i - 3) (i) +
    ((-1/4 : ℚ) + (1/4 : ℚ) * i) * A124431_Cz (n - i - 3) (i) * A124431_Cz (n - i - 3) (i))

theorem A124431_rat (x i : ℚ) (h0 : x - 0 ≠ 0) (h1 : x - 1 ≠ 0) (h2 : x - 2 ≠ 0) (h3 : x - 3 ≠ 0)
    (h4 : x - 4 ≠ 0) (hi : i + 1 ≠ 0) :
    (16*i + 16*x) * ((((x - i) - 0)) / ((x - 0))) * ((((x - i) - 0)) / ((x - 0))) +
      (32*i + 32*x) * ((i * (1)) / ((x - 0))) * ((1) / (1)) +
      (-32*i - 32*x + 16) * ((((x - i) - 0) * ((x - i) - 1)) / ((x - 0) * (x - 1))) * ((((x - i) - 0) * ((x - i) - 1)) / ((x - 0) * (x - 1))) +
      (-64*i - 64*x + 32) * ((i * (((x - i) - 0))) / ((x - 0) * (x - 1))) * ((((x - i) - 0)) / ((x - 0))) +
      (8*i + 8*x - 16) * ((((x - i) - 0) * ((x - i) - 1) * ((x - i) - 2)) / ((x - 0) * (x - 1) * (x - 2))) * ((((x - i) - 0) * ((x - i) - 1) * ((x - i) - 2)) / ((x - 0) * (x - 1) * (x - 2))) +
      (16*i + 16*x - 32) * ((i * (((x - i) - 0) * ((x - i) - 1))) / ((x - 0) * (x - 1) * (x - 2))) * ((((x - i) - 0) * ((x - i) - 1)) / ((x - 0) * (x - 1))) +
      (-8*i - 8*x + 28) * ((((x - i) - 0) * ((x - i) - 1) * ((x - i) - 2) * ((x - i) - 3)) / ((x - 0) * (x - 1) * (x - 2) * (x - 3))) * ((((x - i) - 0) * ((x - i) - 1) * ((x - i) - 2) * ((x - i) - 3)) / ((x - 0) * (x - 1) * (x - 2) * (x - 3))) +
      (-16*i - 16*x + 56) * ((i * (((x - i) - 0) * ((x - i) - 1) * ((x - i) - 2))) / ((x - 0) * (x - 1) * (x - 2) * (x - 3))) * ((((x - i) - 0) * ((x - i) - 1) * ((x - i) - 2)) / ((x - 0) * (x - 1) * (x - 2))) +
      (i + x - 4) * ((((x - i) - 0) * ((x - i) - 1) * ((x - i) - 2) * ((x - i) - 3) * ((x - i) - 4)) / ((x - 0) * (x - 1) * (x - 2) * (x - 3) * (x - 4))) * ((((x - i) - 0) * ((x - i) - 1) * ((x - i) - 2) * ((x - i) - 3) * ((x - i) - 4)) / ((x - 0) * (x - 1) * (x - 2) * (x - 3) * (x - 4))) +
      (2*i + 2*x - 8) * ((i * (((x - i) - 0) * ((x - i) - 1) * ((x - i) - 2) * ((x - i) - 3))) / ((x - 0) * (x - 1) * (x - 2) * (x - 3) * (x - 4))) * ((((x - i) - 0) * ((x - i) - 1) * ((x - i) - 2) * ((x - i) - 3)) / ((x - 0) * (x - 1) * (x - 2) * (x - 3))) +
      (-16*i - 20) * (((((x - i) - 0) * ((x - i) - 1)) * ((x - i) - 2)) / ((i + 1) * ((x - 0) * (x - 1)))) * (((((x - i) - 0) * ((x - i) - 1)) * ((x - i) - 2)) / ((i + 1) * ((x - 0) * (x - 1)))) +
      (64*i + 16) * ((((x - i) - 0)) / ((x - 0))) * ((((x - i) - 0)) / ((x - 0))) +
      (24*i + 24) * (((((x - i) - 0) * ((x - i) - 1)) * ((x - i) - 2)) / ((i + 1) * ((x - 0) * (x - 1)))) * ((((x - i) - 0) * ((x - i) - 1)) / ((x - 0) * (x - 1))) +
      (-96*i) * ((((x - i) - 0)) / ((x - 0))) * ((i * (1)) / ((x - 0))) +
      (16*i + 16) * ((((x - i) - 0) * ((x - i) - 1)) / ((x - 0) * (x - 1))) * ((((x - i) - 0) * ((x - i) - 1)) / ((x - 0) * (x - 1))) +
      (-64*i) * ((i * (1)) / ((x - 0))) * ((i * (1)) / ((x - 0))) +
      (20*i + 28) * (((((x - i) - 0) * ((x - i) - 1)) * ((x - i) - 2)) / ((i + 1) * ((x - 0) * (x - 1)))) * (((((x - i) - 0) * ((x - i) - 1) * ((x - i) - 2)) * ((x - i) - 3)) / ((i + 1) * ((x - 0) * (x - 1) * (x - 2)))) +
      (-80*i - 32) * ((((x - i) - 0)) / ((x - 0))) * ((((x - i) - 0) * ((x - i) - 1)) / ((x - 0) * (x - 1))) +
      (2) * (((((x - i) - 0) * ((x - i) - 1)) * ((x - i) - 2)) / ((i + 1) * ((x - 0) * (x - 1)))) * (((((x - i) - 0) * ((x - i) - 1) * ((x - i) - 2) * ((x - i) - 3)) * ((x - i) - 4)) / ((i + 1) * ((x - 0) * (x - 1) * (x - 2) * (x - 3)))) +
      (-8) * ((((x - i) - 0)) / ((x - 0))) * ((((x - i) - 0) * ((x - i) - 1) * ((x - i) - 2)) / ((x - 0) * (x - 1) * (x - 2))) +
      (i - 1) * (((((x - i) - 0) * ((x - i) - 1)) * ((x - i) - 2)) / ((i + 1) * ((x - 0) * (x - 1)))) * (((((x - i) - 0) * ((x - i) - 1) * ((x - i) - 2) * ((x - i) - 3) * ((x - i) - 4)) * ((x - i) - 5)) / ((i + 1) * ((x - 0) * (x - 1) * (x - 2) * (x - 3) * (x - 4)))) +
      (8 - 4*i) * ((((x - i) - 0)) / ((x - 0))) * ((((x - i) - 0) * ((x - i) - 1) * ((x - i) - 2) * ((x - i) - 3)) / ((x - 0) * (x - 1) * (x - 2) * (x - 3))) +
      (-4) * (((((x - i) - 0) * ((x - i) - 1) * ((x - i) - 2)) * ((x - i) - 3)) / ((i + 1) * ((x - 0) * (x - 1) * (x - 2)))) * (((((x - i) - 0) * ((x - i) - 1) * ((x - i) - 2)) * ((x - i) - 3)) / ((i + 1) * ((x - 0) * (x - 1) * (x - 2)))) +
      (16) * ((((x - i) - 0) * ((x - i) - 1)) / ((x - 0) * (x - 1))) * ((((x - i) - 0) * ((x - i) - 1)) / ((x - 0) * (x - 1))) +
      (-3*i - 3) * (((((x - i) - 0) * ((x - i) - 1) * ((x - i) - 2)) * ((x - i) - 3)) / ((i + 1) * ((x - 0) * (x - 1) * (x - 2)))) * (((((x - i) - 0) * ((x - i) - 1) * ((x - i) - 2) * ((x - i) - 3)) * ((x - i) - 4)) / ((i + 1) * ((x - 0) * (x - 1) * (x - 2) * (x - 3)))) +
      (12*i) * ((((x - i) - 0) * ((x - i) - 1)) / ((x - 0) * (x - 1))) * ((((x - i) - 0) * ((x - i) - 1) * ((x - i) - 2)) / ((x - 0) * (x - 1) * (x - 2))) +
      (2*i + 2) * (((((x - i) - 0) * ((x - i) - 1) * ((x - i) - 2)) * ((x - i) - 3)) / ((i + 1) * ((x - 0) * (x - 1) * (x - 2)))) * (((((x - i) - 0) * ((x - i) - 1) * ((x - i) - 2) * ((x - i) - 3) * ((x - i) - 4)) * ((x - i) - 5)) / ((i + 1) * ((x - 0) * (x - 1) * (x - 2) * (x - 3) * (x - 4)))) +
      (-8*i) * ((((x - i) - 0) * ((x - i) - 1)) / ((x - 0) * (x - 1))) * ((((x - i) - 0) * ((x - i) - 1) * ((x - i) - 2) * ((x - i) - 3)) / ((x - 0) * (x - 1) * (x - 2) * (x - 3))) +
      (-8*i - 9) * (((((x - i) - 0) * ((x - i) - 1) * ((x - i) - 2) * ((x - i) - 3)) * ((x - i) - 4)) / ((i + 1) * ((x - 0) * (x - 1) * (x - 2) * (x - 3)))) * (((((x - i) - 0) * ((x - i) - 1) * ((x - i) - 2) * ((x - i) - 3)) * ((x - i) - 4)) / ((i + 1) * ((x - 0) * (x - 1) * (x - 2) * (x - 3)))) +
      (32*i + 4) * ((((x - i) - 0) * ((x - i) - 1) * ((x - i) - 2)) / ((x - 0) * (x - 1) * (x - 2))) * ((((x - i) - 0) * ((x - i) - 1) * ((x - i) - 2)) / ((x - 0) * (x - 1) * (x - 2))) +
      (5*i + 5) * (((((x - i) - 0) * ((x - i) - 1) * ((x - i) - 2) * ((x - i) - 3)) * ((x - i) - 4)) / ((i + 1) * ((x - 0) * (x - 1) * (x - 2) * (x - 3)))) * (((((x - i) - 0) * ((x - i) - 1) * ((x - i) - 2) * ((x - i) - 3) * ((x - i) - 4)) * ((x - i) - 5)) / ((i + 1) * ((x - 0) * (x - 1) * (x - 2) * (x - 3) * (x - 4)))) +
      (-20*i) * ((((x - i) - 0) * ((x - i) - 1) * ((x - i) - 2)) / ((x - 0) * (x - 1) * (x - 2))) * ((((x - i) - 0) * ((x - i) - 1) * ((x - i) - 2) * ((x - i) - 3)) / ((x - 0) * (x - 1) * (x - 2) * (x - 3))) +
      (-i) * (((((x - i) - 0) * ((x - i) - 1) * ((x - i) - 2) * ((x - i) - 3) * ((x - i) - 4)) * ((x - i) - 5)) / ((i + 1) * ((x - 0) * (x - 1) * (x - 2) * (x - 3) * (x - 4)))) * (((((x - i) - 0) * ((x - i) - 1) * ((x - i) - 2) * ((x - i) - 3) * ((x - i) - 4)) * ((x - i) - 5)) / ((i + 1) * ((x - 0) * (x - 1) * (x - 2) * (x - 3) * (x - 4)))) +
      (4*i - 4) * ((((x - i) - 0) * ((x - i) - 1) * ((x - i) - 2) * ((x - i) - 3)) / ((x - 0) * (x - 1) * (x - 2) * (x - 3))) * ((((x - i) - 0) * ((x - i) - 1) * ((x - i) - 2) * ((x - i) - 3)) / ((x - 0) * (x - 1) * (x - 2) * (x - 3))) = 0 := by
  field_simp
  ring

theorem A124431_core (n i : ℤ) (hX : ((n : ℚ) - i + 1) * ((n : ℚ) - i) * ((n : ℚ) - i - 1) *
    ((n : ℚ) - i - 2) * ((n : ℚ) - i - 3) ≠ 0) (hi : (i : ℚ) + 1 ≠ 0) :
    ((n : ℚ) + 1) * A124431_w n i - 2 * (2 * n + 1) * A124431_w (n - 1) i +
      2 * (n - 1) * A124431_w (n - 2) i + 2 * (5 - 2 * n) * A124431_w (n - 3) i +
      (n - 3) * A124431_w (n - 4) i = A124431_G n (i + 1) - A124431_G n i := by
  set S : ℚ := (2 : ℚ) ^ (n - 2 * i - 4) with hS
  have p0 : (2 : ℚ) ^ (n - 2 * i) = S * 16 := by
    rw [hS, show n - 2 * i = (n - 2 * i - 4) + 4 by ring, zpow_add₀ two_ne_zero]
    norm_num
  have p1 : (2 : ℚ) ^ (n - 1 - 2 * i) = S * 8 := by
    rw [hS, show n - 1 - 2 * i = (n - 2 * i - 4) + 3 by ring, zpow_add₀ two_ne_zero]
    norm_num
  have p2 : (2 : ℚ) ^ (n - 2 - 2 * i) = S * 4 := by
    rw [hS, show n - 2 - 2 * i = (n - 2 * i - 4) + 2 by ring, zpow_add₀ two_ne_zero]
    norm_num
  have p3 : (2 : ℚ) ^ (n - 3 - 2 * i) = S * 2 := by
    rw [hS, show n - 3 - 2 * i = (n - 2 * i - 4) + 1 by ring, zpow_add₀ two_ne_zero]
    norm_num
  have p4 : (2 : ℚ) ^ (n - 4 - 2 * i) = S * 1 := by
    rw [hS, show n - 4 - 2 * i = (n - 2 * i - 4) + 0 by ring, zpow_add₀ two_ne_zero]
    norm_num
  have p5 : (2 : ℚ) ^ (n - 2 * (i + 1)) = S * 4 := by
    rw [hS, show n - 2 * (i + 1) = (n - 2 * i - 4) + 2 by ring, zpow_add₀ two_ne_zero]
    norm_num
  simp only [A124431_w, A124431_G]
  rw [p0, p1, p2, p3, p4, p5]
  have r1_0 := A124431_R1 (n - i + 1 - 0) i
  have r1_1 := A124431_R1 (n - i + 1 - 1) i
  have r1_2 := A124431_R1 (n - i + 1 - 2) i
  have r1_3 := A124431_R1 (n - i + 1 - 3) i
  have r1_4 := A124431_R1 (n - i + 1 - 4) i
  have r3_2 := A124431_R3 (n - i + 1 - 2) i
  have r3_3 := A124431_R3 (n - i + 1 - 3) i
  have r3_4 := A124431_R3 (n - i + 1 - 4) i
  have r3_5 := A124431_R3 (n - i + 1 - 5) i
  have r2_1 := A124431_R2 (n - i + 1 - 1 + 1) i
  have r2_2 := A124431_R2 (n - i + 1 - 2 + 1) i
  have r2_3 := A124431_R2 (n - i + 1 - 3 + 1) i
  have r2_4 := A124431_R2 (n - i + 1 - 4 + 1) i
  have r2_5 := A124431_R2 (n - i + 1 - 5 + 1) i
  push_cast at *
  have h1z : A124431_Cz (n - i + 1 - 1) (i) * ((((n : ℚ) - i + 1) - 0)) = A124431_Cz (n - i + 1) (i) * (((((n : ℚ) - i + 1) - (i : ℚ)) - 0)) := by
    linear_combination (norm := ring_nf) 1 * r1_0
  have h2z : A124431_Cz (n - i + 1 - 2) (i) * ((((n : ℚ) - i + 1) - 0) * (((n : ℚ) - i + 1) - 1)) = A124431_Cz (n - i + 1) (i) * (((((n : ℚ) - i + 1) - (i : ℚ)) - 0) * ((((n : ℚ) - i + 1) - (i : ℚ)) - 1)) := by
    linear_combination (norm := ring_nf) 1 * ((((n : ℚ) - i + 1) - (i : ℚ)) - 1) * r1_0 + (((n : ℚ) - i + 1) - 0) * r1_1
  have h3z : A124431_Cz (n - i + 1 - 3) (i) * ((((n : ℚ) - i + 1) - 0) * (((n : ℚ) - i + 1) - 1) * (((n : ℚ) - i + 1) - 2)) = A124431_Cz (n - i + 1) (i) * (((((n : ℚ) - i + 1) - (i : ℚ)) - 0) * ((((n : ℚ) - i + 1) - (i : ℚ)) - 1) * ((((n : ℚ) - i + 1) - (i : ℚ)) - 2)) := by
    linear_combination (norm := ring_nf) 1 * ((((n : ℚ) - i + 1) - (i : ℚ)) - 1) * ((((n : ℚ) - i + 1) - (i : ℚ)) - 2) * r1_0 + (((n : ℚ) - i + 1) - 0) * ((((n : ℚ) - i + 1) - (i : ℚ)) - 2) * r1_1 + (((n : ℚ) - i + 1) - 0) * (((n : ℚ) - i + 1) - 1) * r1_2
  have h4z : A124431_Cz (n - i + 1 - 4) (i) * ((((n : ℚ) - i + 1) - 0) * (((n : ℚ) - i + 1) - 1) * (((n : ℚ) - i + 1) - 2) * (((n : ℚ) - i + 1) - 3)) = A124431_Cz (n - i + 1) (i) * (((((n : ℚ) - i + 1) - (i : ℚ)) - 0) * ((((n : ℚ) - i + 1) - (i : ℚ)) - 1) * ((((n : ℚ) - i + 1) - (i : ℚ)) - 2) * ((((n : ℚ) - i + 1) - (i : ℚ)) - 3)) := by
    linear_combination (norm := ring_nf) 1 * ((((n : ℚ) - i + 1) - (i : ℚ)) - 1) * ((((n : ℚ) - i + 1) - (i : ℚ)) - 2) * ((((n : ℚ) - i + 1) - (i : ℚ)) - 3) * r1_0 + (((n : ℚ) - i + 1) - 0) * ((((n : ℚ) - i + 1) - (i : ℚ)) - 2) * ((((n : ℚ) - i + 1) - (i : ℚ)) - 3) * r1_1 + (((n : ℚ) - i + 1) - 0) * (((n : ℚ) - i + 1) - 1) * ((((n : ℚ) - i + 1) - (i : ℚ)) - 3) * r1_2 + (((n : ℚ) - i + 1) - 0) * (((n : ℚ) - i + 1) - 1) * (((n : ℚ) - i + 1) - 2) * r1_3
  have h5z : A124431_Cz (n - i + 1 - 5) (i) * ((((n : ℚ) - i + 1) - 0) * (((n : ℚ) - i + 1) - 1) * (((n : ℚ) - i + 1) - 2) * (((n : ℚ) - i + 1) - 3) * (((n : ℚ) - i + 1) - 4)) = A124431_Cz (n - i + 1) (i) * (((((n : ℚ) - i + 1) - (i : ℚ)) - 0) * ((((n : ℚ) - i + 1) - (i : ℚ)) - 1) * ((((n : ℚ) - i + 1) - (i : ℚ)) - 2) * ((((n : ℚ) - i + 1) - (i : ℚ)) - 3) * ((((n : ℚ) - i + 1) - (i : ℚ)) - 4)) := by
    linear_combination (norm := ring_nf) 1 * ((((n : ℚ) - i + 1) - (i : ℚ)) - 1) * ((((n : ℚ) - i + 1) - (i : ℚ)) - 2) * ((((n : ℚ) - i + 1) - (i : ℚ)) - 3) * ((((n : ℚ) - i + 1) - (i : ℚ)) - 4) * r1_0 + (((n : ℚ) - i + 1) - 0) * ((((n : ℚ) - i + 1) - (i : ℚ)) - 2) * ((((n : ℚ) - i + 1) - (i : ℚ)) - 3) * ((((n : ℚ) - i + 1) - (i : ℚ)) - 4) * r1_1 + (((n : ℚ) - i + 1) - 0) * (((n : ℚ) - i + 1) - 1) * ((((n : ℚ) - i + 1) - (i : ℚ)) - 3) * ((((n : ℚ) - i + 1) - (i : ℚ)) - 4) * r1_2 + (((n : ℚ) - i + 1) - 0) * (((n : ℚ) - i + 1) - 1) * (((n : ℚ) - i + 1) - 2) * ((((n : ℚ) - i + 1) - (i : ℚ)) - 4) * r1_3 + (((n : ℚ) - i + 1) - 0) * (((n : ℚ) - i + 1) - 1) * (((n : ℚ) - i + 1) - 2) * (((n : ℚ) - i + 1) - 3) * r1_4
  have h1m : A124431_Cz (n - i + 1 - 1) (i - 1) * ((((n : ℚ) - i + 1) - 0)) = A124431_Cz (n - i + 1) (i) * ((i : ℚ) * (1)) := by
    linear_combination (norm := ring_nf) r2_1
  have h2m : A124431_Cz (n - i + 1 - 2) (i - 1) * ((((n : ℚ) - i + 1) - 0) * (((n : ℚ) - i + 1) - 1)) = A124431_Cz (n - i + 1) (i) * ((i : ℚ) * (((((n : ℚ) - i + 1) - (i : ℚ)) - 0))) := by
    linear_combination (norm := ring_nf) ((((n : ℚ) - i + 1) - 0)) * r2_2 + (i : ℚ) * h1z
  have h3m : A124431_Cz (n - i + 1 - 3) (i - 1) * ((((n : ℚ) - i + 1) - 0) * (((n : ℚ) - i + 1) - 1) * (((n : ℚ) - i + 1) - 2)) = A124431_Cz (n - i + 1) (i) * ((i : ℚ) * (((((n : ℚ) - i + 1) - (i : ℚ)) - 0) * ((((n : ℚ) - i + 1) - (i : ℚ)) - 1))) := by
    linear_combination (norm := ring_nf) ((((n : ℚ) - i + 1) - 0) * (((n : ℚ) - i + 1) - 1)) * r2_3 + (i : ℚ) * h2z
  have h4m : A124431_Cz (n - i + 1 - 4) (i - 1) * ((((n : ℚ) - i + 1) - 0) * (((n : ℚ) - i + 1) - 1) * (((n : ℚ) - i + 1) - 2) * (((n : ℚ) - i + 1) - 3)) = A124431_Cz (n - i + 1) (i) * ((i : ℚ) * (((((n : ℚ) - i + 1) - (i : ℚ)) - 0) * ((((n : ℚ) - i + 1) - (i : ℚ)) - 1) * ((((n : ℚ) - i + 1) - (i : ℚ)) - 2))) := by
    linear_combination (norm := ring_nf) ((((n : ℚ) - i + 1) - 0) * (((n : ℚ) - i + 1) - 1) * (((n : ℚ) - i + 1) - 2)) * r2_4 + (i : ℚ) * h3z
  have h5m : A124431_Cz (n - i + 1 - 5) (i - 1) * ((((n : ℚ) - i + 1) - 0) * (((n : ℚ) - i + 1) - 1) * (((n : ℚ) - i + 1) - 2) * (((n : ℚ) - i + 1) - 3) * (((n : ℚ) - i + 1) - 4)) = A124431_Cz (n - i + 1) (i) * ((i : ℚ) * (((((n : ℚ) - i + 1) - (i : ℚ)) - 0) * ((((n : ℚ) - i + 1) - (i : ℚ)) - 1) * ((((n : ℚ) - i + 1) - (i : ℚ)) - 2) * ((((n : ℚ) - i + 1) - (i : ℚ)) - 3))) := by
    linear_combination (norm := ring_nf) ((((n : ℚ) - i + 1) - 0) * (((n : ℚ) - i + 1) - 1) * (((n : ℚ) - i + 1) - 2) * (((n : ℚ) - i + 1) - 3)) * r2_5 + (i : ℚ) * h4z
  have h2p : A124431_Cz (n - i + 1 - 2) (i + 1) * (((i : ℚ) + 1) * ((((n : ℚ) - i + 1) - 0) * (((n : ℚ) - i + 1) - 1))) = A124431_Cz (n - i + 1) (i) * ((((((n : ℚ) - i + 1) - (i : ℚ)) - 0) * ((((n : ℚ) - i + 1) - (i : ℚ)) - 1)) * ((((n : ℚ) - i + 1) - (i : ℚ)) - 2)) := by
    linear_combination (norm := ring_nf) ((((n : ℚ) - i + 1) - 0) * (((n : ℚ) - i + 1) - 1)) * r3_2 + ((((n : ℚ) - i + 1) - (i : ℚ)) - 2) * h2z
  have h3p : A124431_Cz (n - i + 1 - 3) (i + 1) * (((i : ℚ) + 1) * ((((n : ℚ) - i + 1) - 0) * (((n : ℚ) - i + 1) - 1) * (((n : ℚ) - i + 1) - 2))) = A124431_Cz (n - i + 1) (i) * ((((((n : ℚ) - i + 1) - (i : ℚ)) - 0) * ((((n : ℚ) - i + 1) - (i : ℚ)) - 1) * ((((n : ℚ) - i + 1) - (i : ℚ)) - 2)) * ((((n : ℚ) - i + 1) - (i : ℚ)) - 3)) := by
    linear_combination (norm := ring_nf) ((((n : ℚ) - i + 1) - 0) * (((n : ℚ) - i + 1) - 1) * (((n : ℚ) - i + 1) - 2)) * r3_3 + ((((n : ℚ) - i + 1) - (i : ℚ)) - 3) * h3z
  have h4p : A124431_Cz (n - i + 1 - 4) (i + 1) * (((i : ℚ) + 1) * ((((n : ℚ) - i + 1) - 0) * (((n : ℚ) - i + 1) - 1) * (((n : ℚ) - i + 1) - 2) * (((n : ℚ) - i + 1) - 3))) = A124431_Cz (n - i + 1) (i) * ((((((n : ℚ) - i + 1) - (i : ℚ)) - 0) * ((((n : ℚ) - i + 1) - (i : ℚ)) - 1) * ((((n : ℚ) - i + 1) - (i : ℚ)) - 2) * ((((n : ℚ) - i + 1) - (i : ℚ)) - 3)) * ((((n : ℚ) - i + 1) - (i : ℚ)) - 4)) := by
    linear_combination (norm := ring_nf) ((((n : ℚ) - i + 1) - 0) * (((n : ℚ) - i + 1) - 1) * (((n : ℚ) - i + 1) - 2) * (((n : ℚ) - i + 1) - 3)) * r3_4 + ((((n : ℚ) - i + 1) - (i : ℚ)) - 4) * h4z
  have h5p : A124431_Cz (n - i + 1 - 5) (i + 1) * (((i : ℚ) + 1) * ((((n : ℚ) - i + 1) - 0) * (((n : ℚ) - i + 1) - 1) * (((n : ℚ) - i + 1) - 2) * (((n : ℚ) - i + 1) - 3) * (((n : ℚ) - i + 1) - 4))) = A124431_Cz (n - i + 1) (i) * ((((((n : ℚ) - i + 1) - (i : ℚ)) - 0) * ((((n : ℚ) - i + 1) - (i : ℚ)) - 1) * ((((n : ℚ) - i + 1) - (i : ℚ)) - 2) * ((((n : ℚ) - i + 1) - (i : ℚ)) - 3) * ((((n : ℚ) - i + 1) - (i : ℚ)) - 4)) * ((((n : ℚ) - i + 1) - (i : ℚ)) - 5)) := by
    linear_combination (norm := ring_nf) ((((n : ℚ) - i + 1) - 0) * (((n : ℚ) - i + 1) - 1) * (((n : ℚ) - i + 1) - 2) * (((n : ℚ) - i + 1) - 3) * (((n : ℚ) - i + 1) - 4)) * r3_5 + ((((n : ℚ) - i + 1) - (i : ℚ)) - 5) * h5z
  have hx0 : ((n : ℚ) - i + 1) - 0 ≠ 0 := by intro h; apply hX; linear_combination (((n : ℚ) - i) * ((n : ℚ) - i - 1) * ((n : ℚ) - i - 2) * ((n : ℚ) - i - 3)) * h
  have hx1 : ((n : ℚ) - i + 1) - 1 ≠ 0 := by intro h; apply hX; linear_combination (((n : ℚ) - i + 1 - 0) * ((n : ℚ) - i + 1 - 2) * ((n : ℚ) - i + 1 - 3) * ((n : ℚ) - i + 1 - 4)) * h
  have hx2 : ((n : ℚ) - i + 1) - 2 ≠ 0 := by intro h; apply hX; linear_combination (((n : ℚ) - i + 1 - 0) * ((n : ℚ) - i + 1 - 1) * ((n : ℚ) - i + 1 - 3) * ((n : ℚ) - i + 1 - 4)) * h
  have hx3 : ((n : ℚ) - i + 1) - 3 ≠ 0 := by intro h; apply hX; linear_combination (((n : ℚ) - i + 1 - 0) * ((n : ℚ) - i + 1 - 1) * ((n : ℚ) - i + 1 - 2) * ((n : ℚ) - i + 1 - 4)) * h
  have hx4 : ((n : ℚ) - i + 1) - 4 ≠ 0 := by intro h; apply hX; linear_combination (((n : ℚ) - i + 1 - 0) * ((n : ℚ) - i + 1 - 1) * ((n : ℚ) - i + 1 - 2) * ((n : ℚ) - i + 1 - 3)) * h
  have eh1m : A124431_Cz (n - i + 1 - 1) (i - 1) = A124431_Cz (n - i + 1) (i) * (((i : ℚ) * (1)) / ((((n : ℚ) - i + 1) - 0))) := by
    rw [mul_div_assoc', eq_div_iff (by assumption)]
    exact h1m
  have eh1z : A124431_Cz (n - i + 1 - 1) (i) = A124431_Cz (n - i + 1) (i) * ((((((n : ℚ) - i + 1) - (i : ℚ)) - 0)) / ((((n : ℚ) - i + 1) - 0))) := by
    rw [mul_div_assoc', eq_div_iff (by assumption)]
    exact h1z
  have eh2m : A124431_Cz (n - i + 1 - 2) (i - 1) = A124431_Cz (n - i + 1) (i) * (((i : ℚ) * (((((n : ℚ) - i + 1) - (i : ℚ)) - 0))) / ((((n : ℚ) - i + 1) - 0) * (((n : ℚ) - i + 1) - 1))) := by
    rw [mul_div_assoc', eq_div_iff (by (repeat' apply mul_ne_zero) <;> assumption)]
    exact h2m
  have eh2z : A124431_Cz (n - i + 1 - 2) (i) = A124431_Cz (n - i + 1) (i) * ((((((n : ℚ) - i + 1) - (i : ℚ)) - 0) * ((((n : ℚ) - i + 1) - (i : ℚ)) - 1)) / ((((n : ℚ) - i + 1) - 0) * (((n : ℚ) - i + 1) - 1))) := by
    rw [mul_div_assoc', eq_div_iff (by (repeat' apply mul_ne_zero) <;> assumption)]
    exact h2z
  have eh2p : A124431_Cz (n - i + 1 - 2) (i + 1) = A124431_Cz (n - i + 1) (i) * (((((((n : ℚ) - i + 1) - (i : ℚ)) - 0) * ((((n : ℚ) - i + 1) - (i : ℚ)) - 1)) * ((((n : ℚ) - i + 1) - (i : ℚ)) - 2)) / (((i : ℚ) + 1) * ((((n : ℚ) - i + 1) - 0) * (((n : ℚ) - i + 1) - 1)))) := by
    rw [mul_div_assoc', eq_div_iff (by (repeat' apply mul_ne_zero) <;> assumption)]
    exact h2p
  have eh3m : A124431_Cz (n - i + 1 - 3) (i - 1) = A124431_Cz (n - i + 1) (i) * (((i : ℚ) * (((((n : ℚ) - i + 1) - (i : ℚ)) - 0) * ((((n : ℚ) - i + 1) - (i : ℚ)) - 1))) / ((((n : ℚ) - i + 1) - 0) * (((n : ℚ) - i + 1) - 1) * (((n : ℚ) - i + 1) - 2))) := by
    rw [mul_div_assoc', eq_div_iff (by (repeat' apply mul_ne_zero) <;> assumption)]
    exact h3m
  have eh3z : A124431_Cz (n - i + 1 - 3) (i) = A124431_Cz (n - i + 1) (i) * ((((((n : ℚ) - i + 1) - (i : ℚ)) - 0) * ((((n : ℚ) - i + 1) - (i : ℚ)) - 1) * ((((n : ℚ) - i + 1) - (i : ℚ)) - 2)) / ((((n : ℚ) - i + 1) - 0) * (((n : ℚ) - i + 1) - 1) * (((n : ℚ) - i + 1) - 2))) := by
    rw [mul_div_assoc', eq_div_iff (by (repeat' apply mul_ne_zero) <;> assumption)]
    exact h3z
  have eh3p : A124431_Cz (n - i + 1 - 3) (i + 1) = A124431_Cz (n - i + 1) (i) * (((((((n : ℚ) - i + 1) - (i : ℚ)) - 0) * ((((n : ℚ) - i + 1) - (i : ℚ)) - 1) * ((((n : ℚ) - i + 1) - (i : ℚ)) - 2)) * ((((n : ℚ) - i + 1) - (i : ℚ)) - 3)) / (((i : ℚ) + 1) * ((((n : ℚ) - i + 1) - 0) * (((n : ℚ) - i + 1) - 1) * (((n : ℚ) - i + 1) - 2)))) := by
    rw [mul_div_assoc', eq_div_iff (by (repeat' apply mul_ne_zero) <;> assumption)]
    exact h3p
  have eh4m : A124431_Cz (n - i + 1 - 4) (i - 1) = A124431_Cz (n - i + 1) (i) * (((i : ℚ) * (((((n : ℚ) - i + 1) - (i : ℚ)) - 0) * ((((n : ℚ) - i + 1) - (i : ℚ)) - 1) * ((((n : ℚ) - i + 1) - (i : ℚ)) - 2))) / ((((n : ℚ) - i + 1) - 0) * (((n : ℚ) - i + 1) - 1) * (((n : ℚ) - i + 1) - 2) * (((n : ℚ) - i + 1) - 3))) := by
    rw [mul_div_assoc', eq_div_iff (by (repeat' apply mul_ne_zero) <;> assumption)]
    exact h4m
  have eh4z : A124431_Cz (n - i + 1 - 4) (i) = A124431_Cz (n - i + 1) (i) * ((((((n : ℚ) - i + 1) - (i : ℚ)) - 0) * ((((n : ℚ) - i + 1) - (i : ℚ)) - 1) * ((((n : ℚ) - i + 1) - (i : ℚ)) - 2) * ((((n : ℚ) - i + 1) - (i : ℚ)) - 3)) / ((((n : ℚ) - i + 1) - 0) * (((n : ℚ) - i + 1) - 1) * (((n : ℚ) - i + 1) - 2) * (((n : ℚ) - i + 1) - 3))) := by
    rw [mul_div_assoc', eq_div_iff (by (repeat' apply mul_ne_zero) <;> assumption)]
    exact h4z
  have eh4p : A124431_Cz (n - i + 1 - 4) (i + 1) = A124431_Cz (n - i + 1) (i) * (((((((n : ℚ) - i + 1) - (i : ℚ)) - 0) * ((((n : ℚ) - i + 1) - (i : ℚ)) - 1) * ((((n : ℚ) - i + 1) - (i : ℚ)) - 2) * ((((n : ℚ) - i + 1) - (i : ℚ)) - 3)) * ((((n : ℚ) - i + 1) - (i : ℚ)) - 4)) / (((i : ℚ) + 1) * ((((n : ℚ) - i + 1) - 0) * (((n : ℚ) - i + 1) - 1) * (((n : ℚ) - i + 1) - 2) * (((n : ℚ) - i + 1) - 3)))) := by
    rw [mul_div_assoc', eq_div_iff (by (repeat' apply mul_ne_zero) <;> assumption)]
    exact h4p
  have eh5m : A124431_Cz (n - i + 1 - 5) (i - 1) = A124431_Cz (n - i + 1) (i) * (((i : ℚ) * (((((n : ℚ) - i + 1) - (i : ℚ)) - 0) * ((((n : ℚ) - i + 1) - (i : ℚ)) - 1) * ((((n : ℚ) - i + 1) - (i : ℚ)) - 2) * ((((n : ℚ) - i + 1) - (i : ℚ)) - 3))) / ((((n : ℚ) - i + 1) - 0) * (((n : ℚ) - i + 1) - 1) * (((n : ℚ) - i + 1) - 2) * (((n : ℚ) - i + 1) - 3) * (((n : ℚ) - i + 1) - 4))) := by
    rw [mul_div_assoc', eq_div_iff (by (repeat' apply mul_ne_zero) <;> assumption)]
    exact h5m
  have eh5z : A124431_Cz (n - i + 1 - 5) (i) = A124431_Cz (n - i + 1) (i) * ((((((n : ℚ) - i + 1) - (i : ℚ)) - 0) * ((((n : ℚ) - i + 1) - (i : ℚ)) - 1) * ((((n : ℚ) - i + 1) - (i : ℚ)) - 2) * ((((n : ℚ) - i + 1) - (i : ℚ)) - 3) * ((((n : ℚ) - i + 1) - (i : ℚ)) - 4)) / ((((n : ℚ) - i + 1) - 0) * (((n : ℚ) - i + 1) - 1) * (((n : ℚ) - i + 1) - 2) * (((n : ℚ) - i + 1) - 3) * (((n : ℚ) - i + 1) - 4))) := by
    rw [mul_div_assoc', eq_div_iff (by (repeat' apply mul_ne_zero) <;> assumption)]
    exact h5z
  have eh5p : A124431_Cz (n - i + 1 - 5) (i + 1) = A124431_Cz (n - i + 1) (i) * (((((((n : ℚ) - i + 1) - (i : ℚ)) - 0) * ((((n : ℚ) - i + 1) - (i : ℚ)) - 1) * ((((n : ℚ) - i + 1) - (i : ℚ)) - 2) * ((((n : ℚ) - i + 1) - (i : ℚ)) - 3) * ((((n : ℚ) - i + 1) - (i : ℚ)) - 4)) * ((((n : ℚ) - i + 1) - (i : ℚ)) - 5)) / (((i : ℚ) + 1) * ((((n : ℚ) - i + 1) - 0) * (((n : ℚ) - i + 1) - 1) * (((n : ℚ) - i + 1) - 2) * (((n : ℚ) - i + 1) - 3) * (((n : ℚ) - i + 1) - 4)))) := by
    rw [mul_div_assoc', eq_div_iff (by (repeat' apply mul_ne_zero) <;> assumption)]
    exact h5p
  have st : (16*(n : ℚ) + 16) * A124431_Cz (n - i + 1 - 1) (i) * A124431_Cz (n - i + 1 - 1) (i) + (32*(n : ℚ) + 32) * A124431_Cz (n - i + 1 - 1) (i - 1) * A124431_Cz (n - i + 1) (i) + (-32*(n : ℚ) - 16) * A124431_Cz (n - i + 1 - 2) (i) * A124431_Cz (n - i + 1 - 2) (i) + (-64*(n : ℚ) - 32) * A124431_Cz (n - i + 1 - 2) (i - 1) * A124431_Cz (n - i + 1 - 1) (i) + (8*(n : ℚ) - 8) * A124431_Cz (n - i + 1 - 3) (i) * A124431_Cz (n - i + 1 - 3) (i) + (16*(n : ℚ) - 16) * A124431_Cz (n - i + 1 - 3) (i - 1) * A124431_Cz (n - i + 1 - 2) (i) + (20 - 8*(n : ℚ)) * A124431_Cz (n - i + 1 - 4) (i) * A124431_Cz (n - i + 1 - 4) (i) + (40 - 16*(n : ℚ)) * A124431_Cz (n - i + 1 - 4) (i - 1) * A124431_Cz (n - i + 1 - 3) (i) + ((n : ℚ) - 3) * A124431_Cz (n - i + 1 - 5) (i) * A124431_Cz (n - i + 1 - 5) (i) + (2*(n : ℚ) - 6) * A124431_Cz (n - i + 1 - 5) (i - 1) * A124431_Cz (n - i + 1 - 4) (i) + (-16*(i : ℚ) - 20) * A124431_Cz (n - i + 1 - 2) (i + 1) * A124431_Cz (n - i + 1 - 2) (i + 1) + (64*(i : ℚ) + 16) * A124431_Cz (n - i + 1 - 1) (i) * A124431_Cz (n - i + 1 - 1) (i) + (24*(i : ℚ) + 24) * A124431_Cz (n - i + 1 - 2) (i + 1) * A124431_Cz (n - i + 1 - 2) (i) + (-96*(i : ℚ)) * A124431_Cz (n - i + 1 - 1) (i) * A124431_Cz (n - i + 1 - 1) (i - 1) + (16*(i : ℚ) + 16) * A124431_Cz (n - i + 1 - 2) (i) * A124431_Cz (n - i + 1 - 2) (i) + (-64*(i : ℚ)) * A124431_Cz (n - i + 1 - 1) (i - 1) * A124431_Cz (n - i + 1 - 1) (i - 1) + (20*(i : ℚ) + 28) * A124431_Cz (n - i + 1 - 2) (i + 1) * A124431_Cz (n - i + 1 - 3) (i + 1) + (-80*(i : ℚ) - 32) * A124431_Cz (n - i + 1 - 1) (i) * A124431_Cz (n - i + 1 - 2) (i) + (2) * A124431_Cz (n - i + 1 - 2) (i + 1) * A124431_Cz (n - i + 1 - 4) (i + 1) + (-8) * A124431_Cz (n - i + 1 - 1) (i) * A124431_Cz (n - i + 1 - 3) (i) + ((i : ℚ) - 1) * A124431_Cz (n - i + 1 - 2) (i + 1) * A124431_Cz (n - i + 1 - 5) (i + 1) + (8 - 4*(i : ℚ)) * A124431_Cz (n - i + 1 - 1) (i) * A124431_Cz (n - i + 1 - 4) (i) + (-4) * A124431_Cz (n - i + 1 - 3) (i + 1) * A124431_Cz (n - i + 1 - 3) (i + 1) + (16) * A124431_Cz (n - i + 1 - 2) (i) * A124431_Cz (n - i + 1 - 2) (i) + (-3*(i : ℚ) - 3) * A124431_Cz (n - i + 1 - 3) (i + 1) * A124431_Cz (n - i + 1 - 4) (i + 1) + (12*(i : ℚ)) * A124431_Cz (n - i + 1 - 2) (i) * A124431_Cz (n - i + 1 - 3) (i) + (2*(i : ℚ) + 2) * A124431_Cz (n - i + 1 - 3) (i + 1) * A124431_Cz (n - i + 1 - 5) (i + 1) + (-8*(i : ℚ)) * A124431_Cz (n - i + 1 - 2) (i) * A124431_Cz (n - i + 1 - 4) (i) + (-8*(i : ℚ) - 9) * A124431_Cz (n - i + 1 - 4) (i + 1) * A124431_Cz (n - i + 1 - 4) (i + 1) + (32*(i : ℚ) + 4) * A124431_Cz (n - i + 1 - 3) (i) * A124431_Cz (n - i + 1 - 3) (i) + (5*(i : ℚ) + 5) * A124431_Cz (n - i + 1 - 4) (i + 1) * A124431_Cz (n - i + 1 - 5) (i + 1) + (-20*(i : ℚ)) * A124431_Cz (n - i + 1 - 3) (i) * A124431_Cz (n - i + 1 - 4) (i) + (-(i : ℚ)) * A124431_Cz (n - i + 1 - 5) (i + 1) * A124431_Cz (n - i + 1 - 5) (i + 1) + (4*(i : ℚ) - 4) * A124431_Cz (n - i + 1 - 4) (i) * A124431_Cz (n - i + 1 - 4) (i) = 0 := by
    rw [eh1m, eh1z, eh2m, eh2z, eh2p, eh3m, eh3z, eh3p, eh4m, eh4z, eh4p, eh5m, eh5z, eh5p]
    linear_combination (A124431_Cz (n - i + 1) (i)) ^ 2 * A124431_rat ((n : ℚ) - i + 1) i hx0 hx1 hx2 hx3 hx4 hi
  linear_combination (norm := ring_nf) S * st

theorem A124431_w_zero {m i : ℤ} (h : m + 2 ≤ 2 * i) : A124431_w m i = 0 := by
  simp only [A124431_w]
  rw [A124431_Cz_lt (by omega), A124431_Cz_lt (by omega)]
  ring

theorem A124431_G_zero {n i : ℤ} (h : n + 2 ≤ 2 * i) : A124431_G n i = 0 := by
  simp only [A124431_G]
  rw [A124431_Cz_lt (by omega : n - i < i), A124431_Cz_lt (by omega : n - i < i - 1),
    A124431_Cz_lt (by omega : n - i - 1 < i), A124431_Cz_lt (by omega : n - i - 2 < i),
    A124431_Cz_lt (by omega : n - i - 3 < i)]
  ring

theorem A124431_G_at_zero {n : ℤ} (h : 3 ≤ n) : A124431_G n 0 = 0 := by
  have c0 : A124431_Cz n 0 = 1 := by unfold A124431_Cz; rw [ite_eq_left ⟨le_refl _, by omega⟩]; simp
  have c1 : A124431_Cz (n - 1) 0 = 1 := by unfold A124431_Cz; rw [ite_eq_left ⟨le_refl _, by omega⟩]; simp
  have c2 : A124431_Cz (n - 2) 0 = 1 := by unfold A124431_Cz; rw [ite_eq_left ⟨le_refl _, by omega⟩]; simp
  have c3 : A124431_Cz (n - 3) 0 = 1 := by unfold A124431_Cz; rw [ite_eq_left ⟨le_refl _, by omega⟩]; simp
  have cm : A124431_Cz n (0 - 1) = 0 := A124431_Cz_negr (by omega)
  simp only [A124431_G, sub_zero, Int.cast_zero, mul_zero, add_zero]
  rw [c0, c1, c2, c3, cm]
  ring

/-- The recurrence for one summand index i, all n ≥ 8. -/
theorem A124431_step (n i : ℕ) (hn : 8 ≤ n) (hi : i < n + 2) :
    ((n : ℚ) + 1) * A124431_w n i - 2 * (2 * n + 1) * A124431_w ((n : ℤ) - 1) i +
      2 * (n - 1) * A124431_w ((n : ℤ) - 2) i + 2 * (5 - 2 * n) * A124431_w ((n : ℤ) - 3) i +
      (n - 3) * A124431_w ((n : ℤ) - 4) i = A124431_G n ((i : ℤ) + 1) - A124431_G n i := by
  rcases Nat.lt_or_ge (i + 3) n with h | h
  · have := A124431_core n i
    push_cast at this
    apply this
    · have h0 : (0 : ℚ) < (n : ℚ) - i - 3 := by
        have : ((i + 3 : ℕ) : ℚ) < n := by exact_mod_cast h
        push_cast at this
        linarith
      have : (0 : ℚ) < ((n : ℚ) - i + 1) * ((n : ℚ) - i) * ((n : ℚ) - i - 1) * ((n : ℚ) - i - 2) * ((n : ℚ) - i - 3) := by
        have h1 : (0 : ℚ) < (n : ℚ) - i - 2 := by linarith
        have h2 : (0 : ℚ) < (n : ℚ) - i - 1 := by linarith
        have h3 : (0 : ℚ) < (n : ℚ) - i := by linarith
        have h4 : (0 : ℚ) < (n : ℚ) - i + 1 := by linarith
        positivity
      exact this.ne'
    · positivity
  · have e : (n : ℤ) + 2 ≤ 2 * i := by omega
    rw [A124431_w_zero (by omega), A124431_w_zero (by omega), A124431_w_zero (by omega),
      A124431_w_zero (by omega), A124431_w_zero (by omega), A124431_G_zero (by omega), A124431_G_zero e]
    ring

/-- A(n) = Σ_{i < n+2} w(n, i). -/
noncomputable def A124431_A (n : ℕ) : ℚ := ∑ i ∈ Finset.range (n + 2), A124431_w n i

theorem A124431_A_ext (n l : ℕ) (hl : l ≤ n) :
    A124431_A (n - l) = ∑ i ∈ Finset.range (n + 2), A124431_w ((n : ℤ) - l) i := by
  unfold A124431_A
  rw [← Finset.sum_range_add_sum_Ico _ (by omega : n - l + 2 ≤ n + 2)]
  have hz : ∑ i ∈ Finset.Ico (n - l + 2) (n + 2), A124431_w ((n : ℤ) - l) i = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rw [Finset.mem_Ico] at hi
    exact A124431_w_zero (by omega)
  rw [hz, add_zero]
  apply Finset.sum_congr rfl
  intro i _
  rw [Nat.cast_sub hl]

theorem A124431_A_rec (n : ℕ) (hn : 8 ≤ n) :
    ((n : ℚ) + 1) * A124431_A n - 2 * (2 * n + 1) * A124431_A (n - 1) +
      2 * (n - 1) * A124431_A (n - 2) + 2 * (5 - 2 * n) * A124431_A (n - 3) +
      (n - 3) * A124431_A (n - 4) = 0 := by
  rw [A124431_A_ext n 1 (by omega), A124431_A_ext n 2 (by omega), A124431_A_ext n 3 (by omega),
    A124431_A_ext n 4 (by omega)]
  unfold A124431_A
  push_cast
  simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  rw [Finset.sum_congr rfl (fun i hi => A124431_step n i hn (Finset.mem_range.mp hi))]
  have := Finset.sum_range_sub (fun i : ℕ => A124431_G n (i : ℤ)) (n + 2)
  push_cast at this
  rw [this, A124431_G_zero (by omega), A124431_G_at_zero (by omega)]
  ring

/-- The OEIS definition: a(n) = Σ_{k=0..n} 2^k C(⌊(n+k)/2⌋, k) C(⌊(n+k+1)/2⌋, k). -/
def A124431_a (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), 2 ^ k * Nat.choose ((n + k) / 2) k * Nat.choose ((n + k + 1) / 2) k

/-- The OEIS summand at an integer index k (0 outside 0 ≤ k ≤ n). -/
noncomputable def A124431_T (n : ℕ) (k : ℤ) : ℚ :=
  if 0 ≤ k ∧ k ≤ n then
    ((2 ^ k.toNat * Nat.choose ((n + k.toNat) / 2) k.toNat * Nat.choose ((n + k.toNat + 1) / 2) k.toNat : ℕ) : ℚ)
  else 0

theorem A124431_T_nat (n k : ℕ) (hk : k ≤ n) :
    A124431_T n k = ((2 ^ k * Nat.choose ((n + k) / 2) k * Nat.choose ((n + k + 1) / 2) k : ℕ) : ℚ) := by
  unfold A124431_T
  rw [ite_eq_left ⟨by positivity, by exact_mod_cast hk⟩]
  simp only [Int.toNat_natCast]

theorem A124431_T_out (n : ℕ) {k : ℤ} (hk : k < 0 ∨ (n : ℤ) < k) : A124431_T n k = 0 := by
  unfold A124431_T
  rw [ite_eq_right (by omega)]

theorem A124431_Cz_eq {x y : ℤ} {p q : ℕ} (hx : x = p) (hy : y = q) :
    A124431_Cz x y = (p.choose q : ℚ) := by
  rw [hx, hy, A124431_Cz_nat]

/-- w(n, i) collects the OEIS summands k = n - 2i and k = n + 1 - 2i. -/
theorem A124431_w_eq (n i : ℕ) :
    A124431_w n i = A124431_T n ((n : ℤ) - 2 * i) + A124431_T n ((n : ℤ) + 1 - 2 * i) := by
  simp only [A124431_w]
  rcases le_or_gt (2 * i) n with h | h
  · obtain ⟨d, hd⟩ : ∃ d, n = 2 * i + d := ⟨n - 2 * i, by omega⟩
    have e0 : (n : ℤ) - 2 * i = (d : ℕ) := by omega
    have c0 : A124431_Cz ((n : ℤ) - i) i = ((i + d).choose d : ℚ) := by
      rw [A124431_Cz_eq (p := i + d) (q := i) (by push_cast; omega) rfl, Nat.choose_symm_add]
    have t0 : A124431_T n ((n : ℤ) - 2 * i) = 2 ^ d * ((i + d).choose d : ℚ) ^ 2 := by
      rw [e0, A124431_T_nat n d (by omega), show (n + d) / 2 = i + d by omega,
        show (n + d + 1) / 2 = i + d by omega]
      push_cast
      ring
    rw [t0, e0, zpow_natCast, c0]
    rcases Nat.eq_zero_or_pos i with hi | hi
    · rw [A124431_T_out n (by omega), A124431_Cz_negr (by omega)]
      ring
    · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
      have c1 : A124431_Cz ((n : ℤ) - ((j + 1 : ℕ) : ℤ)) (((j + 1 : ℕ) : ℤ) - 1) = ((j + 1 + d).choose (d + 1) : ℚ) := by
        rw [A124431_Cz_eq (p := j + (d + 1)) (q := j) (by push_cast; omega) (by push_cast; ring),
          Nat.choose_symm_add, show j + (d + 1) = j + 1 + d by ring]
      have c2 : A124431_Cz ((n : ℤ) - ((j + 1 : ℕ) : ℤ) + 1) ((j + 1 : ℕ) : ℤ) = ((j + 1 + d + 1).choose (d + 1) : ℚ) := by
        rw [A124431_Cz_eq (p := (j + 1) + (d + 1)) (q := j + 1) (by push_cast; omega) rfl,
          Nat.choose_symm_add, show j + 1 + (d + 1) = j + 1 + d + 1 by ring]
      have t1 : A124431_T n ((n : ℤ) + 1 - 2 * ((j + 1 : ℕ) : ℤ)) =
          2 ^ (d + 1) * ((j + 1 + d).choose (d + 1) : ℚ) * ((j + 1 + d + 1).choose (d + 1) : ℚ) := by
        rw [show (n : ℤ) + 1 - 2 * ((j + 1 : ℕ) : ℤ) = ((d + 1 : ℕ) : ℤ) by push_cast; omega,
          A124431_T_nat n (d + 1) (by omega), show (n + (d + 1)) / 2 = j + 1 + d by omega,
          show (n + (d + 1) + 1) / 2 = j + 1 + d + 1 by omega]
        push_cast
        ring
      rw [c1, c2, t1]
      ring
  · rcases Nat.lt_or_ge (n + 1) (2 * i) with h2 | h2
    · rw [A124431_T_out n (by omega), A124431_T_out n (by omega), A124431_Cz_lt (by omega),
        A124431_Cz_lt (by omega)]
      ring
    · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
      have c0 : A124431_Cz ((n : ℤ) - ((j + 1 : ℕ) : ℤ)) ((j + 1 : ℕ) : ℤ) = 0 := A124431_Cz_lt (by omega)
      have c1 : A124431_Cz ((n : ℤ) - ((j + 1 : ℕ) : ℤ)) (((j + 1 : ℕ) : ℤ) - 1) = 1 := by
        rw [A124431_Cz_eq (p := j) (q := j) (by push_cast; omega) (by push_cast; ring), Nat.choose_self]
        simp
      have c2 : A124431_Cz ((n : ℤ) - ((j + 1 : ℕ) : ℤ) + 1) ((j + 1 : ℕ) : ℤ) = 1 := by
        rw [A124431_Cz_eq (p := j + 1) (q := j + 1) (by push_cast; omega) rfl, Nat.choose_self]
        simp
      have t1 : A124431_T n ((n : ℤ) + 1 - 2 * ((j + 1 : ℕ) : ℤ)) = 1 := by
        rw [show (n : ℤ) + 1 - 2 * ((j + 1 : ℕ) : ℤ) = ((0 : ℕ) : ℤ) by push_cast; omega,
          A124431_T_nat n 0 (by omega)]
        simp
      rw [A124431_T_out n (by omega), c0, c1, c2, t1,
        show (n : ℤ) - 2 * ((j + 1 : ℕ) : ℤ) = -1 by push_cast; omega]
      norm_num

theorem A124431_pair (g : ℕ → ℚ) (M : ℕ) :
    ∑ j ∈ Finset.range (2 * M), g j = ∑ i ∈ Finset.range M, (g (2 * i) + g (2 * i + 1)) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [show 2 * (M + 1) = 2 * M + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ, ih,
      Finset.sum_range_succ]
    ring

/-- The OEIS sum equals A(n) = Σ_i w(n, i). -/
theorem A124431_a_eq_A (n : ℕ) : (A124431_a n : ℚ) = A124431_A n := by
  unfold A124431_A
  simp only [A124431_w_eq]
  have h1 := A124431_pair (fun j => A124431_T n ((n : ℤ) + 1 - j)) (n + 2)
  rw [Finset.sum_congr rfl (fun i _ => add_comm _ _)]
  have h2 : ∀ i : ℕ, A124431_T n ((n : ℤ) + 1 - ((2 * i + 1 : ℕ) : ℤ)) = A124431_T n ((n : ℤ) - 2 * i) := by
    intro i
    congr 1
    push_cast
    ring
  have h3 : ∀ i : ℕ, A124431_T n ((n : ℤ) + 1 - ((2 * i : ℕ) : ℤ)) = A124431_T n ((n : ℤ) + 1 - 2 * i) := by
    intro i
    congr 1
  simp only [h2, h3] at h1
  rw [← h1, ← Finset.sum_range_add_sum_Ico _ (by omega : n + 2 ≤ 2 * (n + 2))]
  have hz : ∑ j ∈ Finset.Ico (n + 2) (2 * (n + 2)), A124431_T n ((n : ℤ) + 1 - j) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    rw [Finset.mem_Ico] at hj
    exact A124431_T_out n (by omega)
  rw [hz, add_zero]
  have hr := Finset.sum_range_reflect (fun k : ℕ => A124431_T n (k : ℤ)) (n + 2)
  rw [Finset.sum_congr rfl (fun j hj => by
    rw [show (n : ℤ) + 1 - j = ((n + 2 - 1 - j : ℕ) : ℤ) by
      have := Finset.mem_range.mp hj
      push_cast [Nat.cast_sub (by omega : j ≤ n + 1)]
      omega])]
  rw [hr, Finset.sum_range_succ, A124431_T_out n (by push_cast; omega), add_zero]
  unfold A124431_a
  push_cast
  apply Finset.sum_congr rfl
  intro k hk
  rw [A124431_T_nat n k (by have := Finset.mem_range.mp hk; omega)]
  push_cast
  ring

theorem A124431_small (n : ℕ) (h1 : 4 ≤ n) (h2 : n ≤ 7) :
    ((n : ℤ) + 1) * A124431_a n - 2 * (2 * n + 1) * A124431_a (n - 1) +
      2 * (n - 1) * A124431_a (n - 2) + 2 * (5 - 2 * n) * A124431_a (n - 3) +
      (n - 3) * A124431_a (n - 4) = 0 := by
  interval_cases n <;> decide

/-- Mathar's conjecture: (n+1) a(n) - 2(2n+1) a(n-1) + 2(n-1) a(n-2) + 2(5-2n) a(n-3)
+ (n-3) a(n-4) = 0 for every n ≥ 4. -/
theorem A124431_conjecture (n : ℕ) (hn : 4 ≤ n) :
    ((n : ℤ) + 1) * A124431_a n - 2 * (2 * n + 1) * A124431_a (n - 1) +
      2 * (n - 1) * A124431_a (n - 2) + 2 * (5 - 2 * n) * A124431_a (n - 3) +
      (n - 3) * A124431_a (n - 4) = 0 := by
  rcases Nat.lt_or_ge n 8 with h | h
  · exact A124431_small n hn (by omega)
  · have hq := A124431_A_rec n h
    simp only [← A124431_a_eq_A] at hq
    exact_mod_cast hq

theorem A124431_data : (List.range 12).map A124431_a = [1, 3, 9, 29, 97, 331, 1145, 4001, 14089, 49915, 177713, 635293] := by
  decide
