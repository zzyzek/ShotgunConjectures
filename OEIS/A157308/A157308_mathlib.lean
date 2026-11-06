import Mathlib

/-
OEIS A157308: the o.g.f. A(x) with F(x) = A(x F(x)), where F(x) is the
o.g.f. of A155585 (e.g.f. exp(x)/cosh(x)); equivalently A(x) =
x / serreverse(x F(x)).
Conjecture (Paul D. Hanna, Mar 17 2009): a(m) is odd iff m is a power of 2
or m = 0.

Definitions used here.
* `f n` (A155585) by the recurrence sum_{j even} C(n,j) f(n-j) = 1, which is
  the coefficient form of cosh(x) * E(x) = exp(x) for the e.g.f. E;
  `f_egf` checks that E(x) = sum f(n) x^n/n! satisfies E * cosh = exp as
  power series over ℚ.
* `a n` (A157308) by a(n) = f(n) - sum_{m<n} a(m) [x^(n-m)] F^m, so that
  `a_spec`: sum_{m <= n} a(m) [x^(n-m)] F(x)^m = f(n) for all n, i.e.
  A(x F(x)) = F(x) coefficientwise.

Checked here (Lean 4.35.0, Mathlib):
* `A157308_conjecture`: Odd (a m) ↔ m = 0 ∨ ∃ k, m = 2 ^ k.
* `f_egf`, `a_spec`: the definitions satisfy the defining identities.
Route: f ≡ 1 + x (mod 2) (`f_mod_two`), so [x^k] F^m ≡ C(m,k) (`coeff_pow_mod_two`);
mod 2 the system reads sum_m a(m) C(m, n-m) = [n <= 1], it is triangular,
and b(m) = [m = 0 or m = 2^k] solves it because C(2^k, j) is even for
0 < j < 2^k (`b_sum`).  In series form: B(x) = sum_k x^(2^k) satisfies
B(x + x^2) = x over GF(2), so A ≡ 1 + B.

Not checked here: agreement of `a` with the data terms (certificate/check.py,
36 terms).
-/

open Finset PowerSeries

/-- A155585 by the recurrence of exp(x)/cosh(x). -/
def f (n : ℕ) : ℤ :=
  1 - ∑ i : Fin n, if Even (n - i) then (n.choose i : ℤ) * f i else 0

lemma f_eq (n : ℕ) :
    f n = 1 - ∑ i ∈ range n, if Even (n - i) then (n.choose i : ℤ) * f i else 0 := by
  rw [f, Fin.sum_univ_eq_sum_range (fun i => if Even (n - i) then (n.choose i : ℤ) * f i else 0)]

/-- The o.g.f. of A155585. -/
noncomputable def F : PowerSeries ℤ := PowerSeries.mk f

/-- A157308. -/
noncomputable def a (n : ℕ) : ℤ :=
  f n - ∑ m : Fin n, a m * coeff (n - m) (F ^ (m : ℕ))

lemma a_eq (n : ℕ) : a n = f n - ∑ m ∈ range n, a m * coeff (n - m) (F ^ m) := by
  rw [a, Fin.sum_univ_eq_sum_range (fun m => a m * coeff (n - m) (F ^ m))]

lemma f_zero : f 0 = 1 := by rw [f_eq]; simp

/-- F(x) = A(x F(x)) coefficientwise. -/
theorem a_spec (n : ℕ) : ∑ m ∈ range (n + 1), a m * coeff (n - m) (F ^ m) = f n := by
  rw [sum_range_succ, a_eq n]
  simp [F, f_zero]

lemma f_key (n : ℕ) :
    ∑ i ∈ range (n + 1), (if Even (n - i) then (n.choose i : ℤ) * f i else 0) = 1 := by
  rw [sum_range_succ, f_eq n]
  simp

/-- E(x) cosh(x) = exp(x) for E(x) = ∑ f(n) x^n / n!. -/
theorem f_egf :
    PowerSeries.mk (fun n => (f n : ℚ) / n.factorial) *
      PowerSeries.mk (fun n => if Even n then (1 : ℚ) / n.factorial else 0) =
      PowerSeries.exp ℚ := by
  ext n
  rw [coeff_mul, coeff_exp, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [coeff_mk, Algebra.algebraMap_self, RingHom.id_apply]
  have hn : (n.factorial : ℚ) ≠ 0 := by positivity
  have key : ((∑ i ∈ range (n + 1),
      (if Even (n - i) then (n.choose i : ℤ) * f i else 0) : ℤ) : ℚ) = 1 := by
    exact_mod_cast f_key n
  rw [eq_div_iff hn, sum_mul]
  refine Eq.trans ?_ key
  push_cast
  apply sum_congr rfl
  intro i hi
  have hi' : i ≤ n := Nat.lt_succ_iff.1 (mem_range.1 hi)
  split_ifs with h
  · have hc : (n.choose i : ℚ) * i.factorial * (n - i).factorial = n.factorial := by
      exact_mod_cast Nat.choose_mul_factorial_mul_factorial hi'
    have h1 : (i.factorial : ℚ) ≠ 0 := by positivity
    have h2 : ((n - i).factorial : ℚ) ≠ 0 := by positivity
    rw [← hc]
    field_simp
  · simp

lemma f_mod_two (n : ℕ) : (f n : ZMod 2) = if n ≤ 1 then 1 else 0 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [f_eq]
    push_cast
    rcases (show n = 0 ∨ n = 1 ∨ 2 ≤ n by omega) with rfl | rfl | hn
    · simp
    · simp
    · rw [ite_eq_right (by omega)]
      have hs : ∀ i ∈ range n, (if Even (n - i) then ((n.choose i : ℕ) : ZMod 2) * ((f i : ℤ) : ZMod 2)
          else 0) =
          (if i = 0 then (if Even n then (1 : ZMod 2) else 0) else 0) +
            (if i = 1 then (if Even (n - 1) then (n : ZMod 2) else 0) else 0) := by
        intro i hi
        have hi' := mem_range.1 hi
        rw [ih i hi']
        rcases (show i = 0 ∨ i = 1 ∨ 2 ≤ i by omega) with rfl | rfl | h2
        · simp
        · simp
        · simp [show ¬ i ≤ 1 by omega, show i ≠ 0 by omega, show i ≠ 1 by omega]
      rw [sum_congr rfl hs, sum_add_distrib, sum_ite_eq' (range n) 0,
        ite_eq_left (mem_range.2 (by omega)), sum_ite_eq' (range n) 1,
        ite_eq_left (mem_range.2 (by omega))]
      rcases Nat.even_or_odd n with he | ho
      · have : ¬ Even (n - 1) := by
          rw [Nat.not_even_iff_odd]; exact Nat.Even.sub_odd (by omega) he odd_one
        simp [he, this]
      · have : Even (n - 1) := Nat.Odd.sub_odd ho odd_one
        have hne : ¬ Even n := Nat.not_even_iff_odd.2 ho
        have : (n : ZMod 2) = 1 := (ZMod.natCast_eq_one_iff_odd).2 ho
        simp [*]

lemma map_F : PowerSeries.map (Int.castRingHom (ZMod 2)) F = 1 + X := by
  ext n
  simp only [coeff_map, F, coeff_mk, eq_intCast, f_mod_two, map_add, coeff_one, coeff_X]
  rcases (show n = 0 ∨ n = 1 ∨ 2 ≤ n by omega) with rfl | rfl | h
  · simp
  · simp
  · simp [show ¬ n ≤ 1 by omega, show n ≠ 0 by omega, show n ≠ 1 by omega]

lemma coeff_pow_mod_two (m k : ℕ) :
    ((coeff k (F ^ m) : ℤ) : ZMod 2) = (m.choose k : ZMod 2) := by
  have h1 : ((coeff k (F ^ m) : ℤ) : ZMod 2) =
      coeff k ((PowerSeries.map (Int.castRingHom (ZMod 2)) F) ^ m) := by
    rw [← map_pow, coeff_map]; rfl
  have h2 : ((1 : PowerSeries (ZMod 2)) + X) = ((1 + Polynomial.X : Polynomial (ZMod 2)) :
      PowerSeries (ZMod 2)) := by
    simp
  rw [h1, map_F, h2, ← Polynomial.coe_pow, Polynomial.coeff_coe, Polynomial.coeff_one_add_X_pow]

open scoped Classical

/-- The claimed parity pattern. -/
noncomputable def b (m : ℕ) : ZMod 2 := if m = 0 ∨ ∃ k, m = 2 ^ k then 1 else 0

lemma choose_two_pow_mod (k j : ℕ) :
    ((2 ^ k).choose j : ZMod 2) = if j = 0 ∨ j = 2 ^ k then 1 else 0 := by
  rcases (show j = 0 ∨ j = 2 ^ k ∨ (j ≠ 0 ∧ j ≠ 2 ^ k) by tauto) with rfl | rfl | ⟨h1, h2⟩
  · simp
  · simp
  · rw [ite_eq_right (by tauto)]
    rw [ZMod.natCast_eq_zero_iff]
    exact Nat.Prime.dvd_choose_pow Nat.prime_two h1 h2

lemma pow_two_inj {k l : ℕ} (h : 2 ^ k = 2 ^ l) : k = l :=
  Nat.pow_right_injective le_rfl h

/-- For n ≥ 1, ∑_{m < n} b(m) C(m, n - m) = [n = 2 m with m a power of 2]. -/
lemma b_sum (n : ℕ) (hn : 1 ≤ n) :
    ∑ m ∈ range n, b m * (m.choose (n - m) : ZMod 2) =
      if ∃ k, n = 2 ^ (k + 1) then 1 else 0 := by
  have hterm : ∀ m ∈ range n, b m * (m.choose (n - m) : ZMod 2) =
      if m = n / 2 ∧ (∃ k, n = 2 ^ (k + 1)) then 1 else 0 := by
    intro m hm
    have hm' := mem_range.1 hm
    unfold b
    by_cases h0 : m = 0
    · subst h0
      simp only [true_or, ↓reduceIte, one_mul]
      rw [Nat.choose_eq_zero_of_lt (by omega)]
      rw [ite_eq_right]; · simp
      rintro ⟨h1, k, hk⟩
      have : 2 ^ (k + 1) ≥ 2 := Nat.le_self_pow (by omega) 2 |>.trans' (by norm_num)
      omega
    · by_cases hp : ∃ k, m = 2 ^ k
      · obtain ⟨k, rfl⟩ := hp
        rw [ite_eq_left (Or.inr ⟨k, rfl⟩), one_mul]
        rcases lt_or_ge (2 ^ k) (n - 2 ^ k) with hlt | hge
        · rw [Nat.choose_eq_zero_of_lt hlt, Nat.cast_zero, ite_eq_right]
          rintro ⟨h1, l, hl⟩
          have : n / 2 = 2 ^ l := by rw [hl, pow_succ]; simp
          omega
        · rw [choose_two_pow_mod]
          by_cases he : n - 2 ^ k = 2 ^ k
          · rw [ite_eq_left (Or.inr he), ite_eq_left]
            refine ⟨by omega, k, by rw [pow_succ]; omega⟩
          · rw [ite_eq_right (by omega), ite_eq_right]
            rintro ⟨h1, l, hl⟩
            have : n / 2 = 2 ^ l := by rw [hl, pow_succ]; simp
            omega
      · rw [ite_eq_right (fun h => h.elim h0 hp), zero_mul, ite_eq_right]
        rintro ⟨h1, l, hl⟩
        apply hp
        refine ⟨l, ?_⟩
        rw [h1, hl, pow_succ]; simp
  rw [sum_congr rfl hterm]
  by_cases hc : ∃ k, n = 2 ^ (k + 1)
  · rw [ite_eq_left hc]
    have : ∀ m ∈ range n, (if m = n / 2 ∧ (∃ k, n = 2 ^ (k + 1)) then (1 : ZMod 2) else 0) =
        if n / 2 = m then 1 else 0 := by
      intro m _
      by_cases h : m = n / 2
      · simp [h, hc]
      · simp [h, Ne.symm h]
    rw [sum_congr rfl this, sum_ite_eq, ite_eq_left (mem_range.2 (by omega))]
  · rw [ite_eq_right hc]
    apply sum_eq_zero
    intro m _
    rw [ite_eq_right (by tauto)]

lemma a_mod_two (n : ℕ) : (a n : ZMod 2) = b n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [a_eq]
    push_cast
    rw [f_mod_two]
    have hs : ∀ m ∈ range n, ((a m : ℤ) : ZMod 2) * ((coeff (n - m) (F ^ m) : ℤ) : ZMod 2) =
        b m * (m.choose (n - m) : ZMod 2) := by
      intro m hm
      rw [ih m (mem_range.1 hm), coeff_pow_mod_two]
    rw [sum_congr rfl hs]
    rcases (show n = 0 ∨ n = 1 ∨ 2 ≤ n by omega) with rfl | rfl | hn
    · simp [b]
    · simp [b]; exact ⟨0, rfl⟩
    · rw [b_sum n (by omega), ite_eq_right (by omega)]
      unfold b
      by_cases hc : ∃ k, n = 2 ^ (k + 1)
      · obtain ⟨k, hk⟩ := hc
        rw [ite_eq_left ⟨k, hk⟩, ite_eq_left (Or.inr ⟨k + 1, hk⟩)]
        decide
      · rw [ite_eq_right hc, ite_eq_right]
        · simp
        rintro (h | ⟨k, hk⟩)
        · omega
        · rcases k with _ | k
          · simp at hk; omega
          · exact hc ⟨k, hk⟩

/-- Hanna's conjecture in A157308. -/
theorem A157308_conjecture (m : ℕ) : Odd (a m) ↔ (m = 0 ∨ ∃ k, m = 2 ^ k) := by
  rw [← ZMod.intCast_eq_one_iff_odd, a_mod_two]
  unfold b
  split_ifs with h
  · simp [h]
  · simp [h]
