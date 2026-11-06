/-
OEIS A202943: G.f. A(x) = [Sum_{n>=0} (n+1)(n+2)/2 * 2^(n(n-1)) x^n]^(1/3).
Conjecture (entry): the characteristic function of a(n) mod 2 equals
(1+x)(1+x^2)(1+x^8) * Sum_n x^(32*A000695(n)), A000695 = sums of distinct powers of 4.

Definitions.
* `B` = Sum (n+1)(n+2)/2 * 2^(n(n-1)) x^n in ℤ⟦X⟧ (A202944).
* `isA695 m`: the base-4 digits of m are 0 or 1 (A000695).
* `charSet n`: n = e + 32 m with e ∈ {0,1,2,3,8,9,10,11} and isA695 m, i.e. x^n
  occurs in (1+x)(1+x^2)(1+x^8) Sum x^(32 A000695(n)).

Main theorems.
* `coeff_sq`: over ZMod 2, [x^n] f^2 = f_{n/2} (n even), 0 (n odd).
* `parity`: if A ∈ ℤ⟦X⟧ and A^3 = B then a(n) mod 2 = tz(n/4), where tz m = 1 iff m
  has no 1-bit at an even position. Route: A^3 = 1 + x mod 2, so A^4 = A(1+x), and
  [x^n] A^4 = a(n/4) [4 | n], giving a(n) = a(n-1) + [4|n] a(n/4) mod 2.
* `charSet_iff`, `A202943_conjecture`: Odd (a n) ↔ charSet n, for any integer cube root A of B.
* `cube_root_unique`: cube roots with constant term 1 are unique in ℚ⟦X⟧, so an integer
  cube root of B is the series of the entry.

* Integrality: `Aseq` adds one coefficient at a time, d = (b(m) - [x^m] A^3)/3; the
  division is exact because b(m) = C(m+2,2) (mod 9) (`b_mod9`) and [x^m] A^3 =
  C(m+2,2) - 3 (mod 9) when A = 1 + x + ... (mod 3) (`cube_mod9`, `coeff_G3`).
  `Aint_cube`: Aint^3 = B with Aint ∈ ℤ⟦X⟧.
* `A202943_main`: for the cube root Aq ∈ ℚ⟦X⟧ of B with constant term 1 (the entry's
  definition), every coefficient is an integer z with Odd z ↔ charSet n.

Not checked in this file: that A000695 is read as "base-4 digits in {0,1}"; agreement
with the b-file (certificate/check.py).
-/
import Mathlib

open PowerSeries Finset

namespace A202943

/-- In characteristic 2, the n-th coefficient of f^2 is f_{n/2} for even n and 0 otherwise. -/
lemma coeff_sq (f : PowerSeries (ZMod 2)) (n : ℕ) :
    coeff n (f ^ 2) = if Even n then coeff (n / 2) f else 0 := by
  rw [pow_two, coeff_mul]
  have hinv : ∑ p ∈ (antidiagonal n).filter (fun p : ℕ × ℕ => p.1 ≠ p.2),
      coeff p.1 f * coeff p.2 f = 0 := by
    apply Finset.sum_involution (fun p _ => (p.2, p.1))
    · intro p _
      have : coeff p.2 f * coeff p.1 f = coeff p.1 f * coeff p.2 f := mul_comm _ _
      simp only [this]
      rw [← two_mul]
      have h2 : (2 : ZMod 2) = 0 := rfl
      rw [h2, zero_mul]
    · intro p hp _ h
      rw [Finset.mem_filter] at hp
      exact hp.2 (Prod.mk.inj h).2
    · intro p hp
      rw [Finset.mem_filter, Finset.HasAntidiagonal.mem_antidiagonal] at hp ⊢
      exact ⟨by simp only; omega, fun h => hp.2 h.symm⟩
    · intro p _; rfl
  rw [← Finset.sum_filter_add_sum_filter_not (antidiagonal n) (fun p : ℕ × ℕ => p.1 ≠ p.2),
    hinv, zero_add]
  split_ifs with he
  · have : (antidiagonal n).filter (fun p : ℕ × ℕ => ¬ p.1 ≠ p.2) = {(n / 2, n / 2)} := by
      ext p
      rw [Finset.mem_filter, Finset.HasAntidiagonal.mem_antidiagonal, Finset.mem_singleton]
      obtain ⟨k, hk⟩ := he
      constructor
      · rintro ⟨h1, h2⟩
        rw [not_not] at h2
        ext <;> simp only <;> omega
      · rintro rfl; simp only [ne_eq, not_true_eq_false, not_false_eq_true, and_true]; omega
    rw [this, Finset.sum_singleton]
    generalize coeff (n / 2) f = c
    fin_cases c <;> rfl
  · apply Finset.sum_eq_zero
    intro p hp
    rw [Finset.mem_filter, Finset.HasAntidiagonal.mem_antidiagonal, not_not] at hp
    exfalso; apply he; exact ⟨p.1, by omega⟩

/-- Coefficients of A202943(x)^3 = A202944: (n+1)(n+2)/2 * 2^(n(n-1)). -/
def b (n : ℕ) : ℤ := (((n + 1) * (n + 2) / 2 : ℕ) : ℤ) * 2 ^ (n * (n - 1))

def B : PowerSeries ℤ := PowerSeries.mk b

/-- t m: m has no 1-bit at an even position. -/
def t (m : ℕ) : Bool := if h : m = 0 then true else (m % 2 == 0) && t (m / 4)
decreasing_by omega

lemma t_zero : t 0 = true := by rw [t]; simp

lemma t_pos (m : ℕ) (hm : m ≠ 0) : t m = ((m % 2 == 0) && t (m / 4)) := by
  rw [t]; simp [hm]

def tz (m : ℕ) : ZMod 2 := if t m then 1 else 0

lemma tz_rel (m : ℕ) (hm : 1 ≤ m) : tz m = tz (m - 1) + tz (m / 4) := by
  have h4 : m % 4 = 0 ∨ m % 4 = 1 ∨ m % 4 = 2 ∨ m % 4 = 3 := by omega
  rcases h4 with h | h | h | h
  · have hm1 : m - 1 ≠ 0 := by omega
    rw [tz, tz, tz, t_pos m (by omega), t_pos (m - 1) hm1]
    have e1 : m % 2 = 0 := by omega
    have e2 : (m - 1) % 2 = 1 := by omega
    simp [e1, e2]
  · rw [tz, tz, tz, t_pos m (by omega)]
    have e1 : m % 2 = 1 := by omega
    have e3 : (m - 1) / 4 = m / 4 := by omega
    by_cases hm1 : m - 1 = 0
    · have : m / 4 = 0 := by omega
      rw [hm1, this, t_zero]; simp [e1]; decide
    · rw [t_pos (m - 1) hm1, e3]
      have e2 : (m - 1) % 2 = 0 := by omega
      simp only [e1, e2]
      cases t (m / 4) <;> decide
  · have hm1 : m - 1 ≠ 0 := by omega
    rw [tz, tz, tz, t_pos m (by omega), t_pos (m - 1) hm1]
    have e1 : m % 2 = 0 := by omega
    have e2 : (m - 1) % 2 = 1 := by omega
    simp [e1, e2]
  · have hm1 : m - 1 ≠ 0 := by omega
    rw [tz, tz, tz, t_pos m (by omega), t_pos (m - 1) hm1]
    have e1 : m % 2 = 1 := by omega
    have e2 : (m - 1) % 2 = 0 := by omega
    have e3 : (m - 1) / 4 = m / 4 := by omega
    simp only [e1, e2, e3]
    cases t (m / 4) <;> decide

/-- The claimed parity: s n = 1 iff n has no 1-bit at an even position >= 2. -/
def s (n : ℕ) : ZMod 2 := tz (n / 4)

lemma s_rel (n : ℕ) (hn : 1 ≤ n) : s n = s (n - 1) + (if 4 ∣ n then s (n / 4) else 0) := by
  unfold s
  split_ifs with h4
  · obtain ⟨m, rfl⟩ := h4
    have hm : 1 ≤ m := by omega
    have e1 : 4 * m / 4 = m := by omega
    have e2 : (4 * m - 1) / 4 = m - 1 := by omega
    rw [e1, e2]
    exact tz_rel m hm
  · have : (n - 1) / 4 = n / 4 := by omega
    rw [this, add_zero]

lemma map_B : PowerSeries.map (Int.castRingHom (ZMod 2)) B = 1 + X := by
  ext n
  rw [coeff_map, B, coeff_mk, map_add, coeff_one, coeff_X]
  rcases n with _ | _ | n
  · simp [b]
  · simp [b]; rfl
  · have h2 : (2 : ℤ) ∣ b (n + 2) := by
      unfold b
      apply Dvd.dvd.mul_left
      apply dvd_pow_self
      exact Nat.mul_ne_zero (by omega) (by omega)
    have : ((b (n + 2) : ℤ) : ZMod 2) = 0 := by
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; exact_mod_cast h2
    simp [this]

/-- Parity of any integer cube root of B. -/
theorem parity (A : PowerSeries ℤ) (hA : A ^ 3 = B) (n : ℕ) :
    ((coeff n A : ℤ) : ZMod 2) = s n := by
  set Ab := PowerSeries.map (Int.castRingHom (ZMod 2)) A with hAb
  have hc : ∀ k, ((coeff k A : ℤ) : ZMod 2) = coeff k Ab := fun k => by
    rw [hAb, coeff_map]; rfl
  have h3 : Ab ^ 3 = 1 + X := by rw [hAb, ← map_pow, hA, map_B]
  have h4 : Ab ^ 4 = Ab * (1 + X) := by rw [pow_succ, h3, mul_comm]
  have hrec : ∀ k, 1 ≤ k → coeff k Ab = coeff (k - 1) Ab +
      (if 4 ∣ k then coeff (k / 4) Ab else 0) := by
    intro k hk
    have e := congrArg (coeff k) h4
    rw [show Ab ^ 4 = (Ab ^ 2) ^ 2 by ring, coeff_sq, mul_add, mul_one, map_add] at e
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [coeff_succ_mul_X] at e
    simp only [Nat.add_sub_cancel]
    rw [coeff_sq] at e
    have hfin : (if Even (j + 1) then (if Even ((j + 1) / 2) then coeff ((j + 1) / 2 / 2) Ab
        else 0) else 0) = (if 4 ∣ j + 1 then coeff ((j + 1) / 4) Ab else 0) := by
      by_cases h4 : 4 ∣ j + 1
      · have he : Even (j + 1) := by obtain ⟨c, hc⟩ := h4; exact ⟨2 * c, by omega⟩
        have he2 : Even ((j + 1) / 2) := by obtain ⟨c, hc⟩ := h4; exact ⟨c, by omega⟩
        simp only [he, he2, h4, ↓reduceIte]
        rw [Nat.div_div_eq_div_mul]
      · simp only [h4, ↓reduceIte]
        split_ifs with he he2
        · exfalso; apply h4
          obtain ⟨c, hc⟩ := he; obtain ⟨d, hd⟩ := he2; exact ⟨d, by omega⟩
        · rfl
        · rfl
    rw [hfin] at e
    have : ∀ x y z : ZMod 2, z = x + y → x = y + z := by decide
    exact this _ _ _ e
  have h0 : coeff 0 Ab = 1 := by
    have e : constantCoeff (Ab ^ 3) = constantCoeff (1 + X) := congrArg constantCoeff h3
    rw [map_pow, map_add, map_one, constantCoeff_X, add_zero] at e
    rw [coeff_zero_eq_constantCoeff_apply]
    have key : ∀ c : ZMod 2, c ^ 3 = 1 → c = 1 := by decide
    exact key _ e
  rw [hc]
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; rw [h0]; simp [s, tz, t_zero]
    · rw [hrec n hn, s_rel n hn, ih (n - 1) (by omega)]
      split_ifs with h4
      · rw [ih (n / 4) (by omega)]
      · rfl

/-- A000695 (sums of distinct powers of 4 = base-4 digits in {0, 1}). -/
def isA695 (m : ℕ) : Bool :=
  if h : m = 0 then true else ((m % 4 == 0 || m % 4 == 1) && isA695 (m / 4))
decreasing_by omega

lemma isA695_pos (m : ℕ) (hm : m ≠ 0) :
    isA695 m = ((m % 4 == 0 || m % 4 == 1) && isA695 (m / 4)) := by
  rw [isA695]; simp [hm]

lemma isA695_eq (m : ℕ) : isA695 m = t (m / 2) := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h; rw [isA695, t_zero]; simp
    · rw [isA695_pos m (by omega), ih (m / 4) (by omega)]
      by_cases h1 : m / 2 = 0
      · have : m = 1 := by omega
        subst this; simp [t_zero]
      · rw [t_pos (m / 2) h1, show m / 4 / 2 = m / 2 / 4 by omega]
        have : ((m % 4 == 0 || m % 4 == 1)) = (m / 2 % 2 == 0) := by
          have h4 : m % 4 = 0 ∨ m % 4 = 1 ∨ m % 4 = 2 ∨ m % 4 = 3 := by omega
          rcases h4 with h4 | h4 | h4 | h4 <;>
          · have : m / 2 % 2 = m % 4 / 2 := by omega
            simp [h4, this]
        rw [this]

/-- The exponents of (1+x)(1+x^2)(1+x^8) * Sum_n x^(32 A000695(n)). -/
def charSet (n : ℕ) : Prop :=
  ∃ e ∈ ({0, 1, 2, 3, 8, 9, 10, 11} : Finset ℕ), ∃ m, isA695 m = true ∧ n = e + 32 * m

lemma charSet_iff (n : ℕ) : charSet n ↔ t (n / 4) = true := by
  constructor
  · rintro ⟨e, he, m, hm, rfl⟩
    have he' : e < 32 ∧ e / 4 % 2 = 0 ∧ e / 16 = 0 := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at he
      rcases he with h | h | h | h | h | h | h | h <;> subst h <;> decide
    by_cases hq : (e + 32 * m) / 4 = 0
    · rw [hq, t_zero]
    rw [t_pos _ hq]
    have h1 : (e + 32 * m) / 4 % 2 = 0 := by omega
    have h2 : (e + 32 * m) / 4 / 4 = 2 * m := by omega
    rw [h2]
    simp only [h1, beq_self_eq_true, Bool.true_and]
    by_cases hm0 : m = 0
    · subst hm0; simp [t_zero]
    rw [t_pos _ (by omega), show 2 * m / 4 = m / 2 by omega, ← isA695_eq, hm]
    simp
  · intro ht
    refine ⟨n % 32, ?_, n / 32, ?_, by omega⟩
    · have key : ∀ r < 32, r / 4 % 2 = 0 → r / 16 % 2 = 0 →
          r ∈ ({0, 1, 2, 3, 8, 9, 10, 11} : Finset ℕ) := by decide
      apply key _ (Nat.mod_lt _ (by norm_num))
      · by_cases hq : n / 4 = 0
        · omega
        rw [t_pos _ hq] at ht
        simp only [Bool.and_eq_true, beq_iff_eq] at ht
        omega
      · by_cases hq : n / 4 = 0
        · omega
        rw [t_pos _ hq] at ht
        simp only [Bool.and_eq_true, beq_iff_eq] at ht
        by_cases hq2 : n / 4 / 4 = 0
        · omega
        have ht2 := ht.2
        rw [t_pos _ hq2] at ht2
        simp only [Bool.and_eq_true, beq_iff_eq] at ht2
        omega
    · rw [isA695_eq]
      by_cases hq : n / 4 = 0
      · rw [show n / 32 / 2 = 0 by omega, t_zero]
      rw [t_pos _ hq] at ht
      simp only [Bool.and_eq_true, beq_iff_eq] at ht
      by_cases hq2 : n / 4 / 4 = 0
      · rw [show n / 32 / 2 = 0 by omega, t_zero]
      have ht2 := ht.2
      rw [t_pos _ hq2] at ht2
      simp only [Bool.and_eq_true, beq_iff_eq] at ht2
      rw [show n / 32 / 2 = n / 4 / 4 / 4 by omega]
      exact ht2.2

/-- Cube roots with constant term 1 are unique in ℚ⟦X⟧. -/
theorem cube_root_unique (A C : PowerSeries ℚ) (h : A ^ 3 = C ^ 3)
    (hA : constantCoeff A = 1) (hC : constantCoeff C = 1) : A = C := by
  have hfac : (A - C) * (A ^ 2 + A * C + C ^ 2) = 0 := by
    have : (A - C) * (A ^ 2 + A * C + C ^ 2) = A ^ 3 - C ^ 3 := by ring
    rw [this, h, sub_self]
  have hne : A ^ 2 + A * C + C ^ 2 ≠ 0 := by
    intro h0
    have := congrArg constantCoeff h0
    simp [hA, hC] at this
    norm_num at this
  exact sub_eq_zero.1 ((mul_eq_zero.1 hfac).resolve_right hne)

/-- Main theorem: for an integer cube root A of B (the OEIS A202943 g.f.),
a(n) is odd iff x^n occurs in (1+x)(1+x^2)(1+x^8) Sum_n x^(32 A000695(n)). -/
theorem A202943_conjecture (A : PowerSeries ℤ) (hA : A ^ 3 = B) (n : ℕ) :
    Odd (coeff n A) ↔ charSet n := by
  rw [charSet_iff, ← Int.not_even_iff_odd, even_iff_two_dvd,
    show (2 : ℤ) = ((2 : ℕ) : ℤ) by rfl, ← ZMod.intCast_zmod_eq_zero_iff_dvd, parity A hA n]
  unfold s tz
  cases t (n / 4) <;> decide

/-! ## The cube root of B has integer coefficients -/

lemma ite_t {α : Type*} {p : Prop} [Decidable p] (h : p) (a b : α) :
    (if p then a else b) = a := by simp [h]

lemma ite_f {α : Type*} {p : Prop} [Decidable p] (h : ¬ p) (a b : α) :
    (if p then a else b) = b := by simp [h]


/-- c m = (m+1)(m+2)/2. -/
def c (m : ℕ) : ℕ := (m + 1) * (m + 2) / 2

lemma two_c (m : ℕ) : 2 * c m = (m + 1) * (m + 2) :=
  Nat.mul_div_cancel' (Nat.even_mul_succ_self (m + 1)).two_dvd

lemma c_eq_choose (m : ℕ) : c m = (2 + m).choose 2 := by
  rw [Nat.choose_two_right]; unfold c
  congr 1
  rw [show 2 + m - 1 = m + 1 by omega]; ring

lemma b_eq (m : ℕ) : b m = (c m : ℤ) * 2 ^ (m * (m - 1)) := rfl

/-- b m ≡ c m (mod 9). -/
lemma b_mod9 (m : ℕ) : (9 : ℤ) ∣ b m - c m := by
  rw [b_eq, show (c m : ℤ) * 2 ^ (m * (m - 1)) - c m = c m * (2 ^ (m * (m - 1)) - 1) by ring]
  have he : 2 ∣ m * (m - 1) := (Nat.even_mul_pred_self m).two_dvd
  by_cases h3 : 3 ∣ m * (m - 1)
  · obtain ⟨t, ht⟩ := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 2 3) he h3
    rw [ht, pow_mul]
    have h63 : (2 : ℤ) ^ 6 - 1 ∣ ((2 : ℤ) ^ 6) ^ t - 1 ^ t := sub_dvd_pow_sub_pow _ _ _
    rw [one_pow] at h63
    have : (9 : ℤ) ∣ (2 : ℤ) ^ (2 * 3) - 1 := by norm_num
    exact Dvd.dvd.mul_left (this.trans h63) _
  · have hm : m % 3 = 2 := by
      by_contra hne
      apply h3
      rcases (by omega : m % 3 = 0 ∨ m % 3 = 1) with h | h
      · exact Dvd.dvd.mul_right (Nat.dvd_of_mod_eq_zero h) _
      · exact Dvd.dvd.mul_left (Nat.dvd_of_mod_eq_zero (by omega)) _
    have hc3 : 3 ∣ c m := by
      have h1 : 3 ∣ 2 * c m := by
        rw [two_c]; exact Dvd.dvd.mul_right (Nat.dvd_of_mod_eq_zero (by omega)) _
      exact (Nat.Coprime.dvd_of_dvd_mul_left (by norm_num : Nat.Coprime 3 2) h1)
    obtain ⟨s, hs⟩ := he
    have h2 : (3 : ℤ) ∣ 2 ^ (m * (m - 1)) - 1 := by
      rw [hs, pow_mul]
      have h4 : (2 : ℤ) ^ 2 - 1 ∣ ((2 : ℤ) ^ 2) ^ s - 1 ^ s := sub_dvd_pow_sub_pow _ _ _
      rw [one_pow] at h4
      exact (by norm_num : (3 : ℤ) ∣ 2 ^ 2 - 1).trans h4
    have := mul_dvd_mul (Int.natCast_dvd_natCast.2 hc3) h2
    simpa using this

/-- G m = 1 + x + ... + x^(m-1). -/
def G (m : ℕ) : PowerSeries ℤ := PowerSeries.mk (fun j => if j < m then 1 else 0)

lemma coeff_G3 (m : ℕ) (hm : 1 ≤ m) : coeff m ((G m) ^ 3) = (c m : ℤ) - 3 := by
  set H : PowerSeries ℤ := PowerSeries.mk (fun n => ((2 + n).choose 2 : ℤ)) with hH
  have hG : G m = (1 - X ^ m) * PowerSeries.mk 1 := by
    ext j
    rw [G, coeff_mk, sub_mul, one_mul, map_sub, coeff_X_pow_mul', coeff_mk]
    split_ifs with h1 h2 h2
    · omega
    · simp
    · simp
    · omega
  have hmk : (PowerSeries.mk 1 : PowerSeries ℤ) ^ 3 = H := by
    rw [hH, show (3 : ℕ) = 2 + 1 from rfl, mk_one_pow_eq_mk_choose_add]
  have hC : (C (3 : ℤ) : PowerSeries ℤ) = 3 := map_ofNat _ _
  have hexp : (G m) ^ 3 = H - C 3 * (X ^ m * H) + C 3 * (X ^ (m + m) * H) - X ^ (m + m + m) * H := by
    rw [hG, mul_pow, hmk, hC]; ring
  rw [hexp, map_sub, map_add, map_sub, coeff_C_mul, coeff_C_mul, coeff_X_pow_mul', coeff_X_pow_mul',
    coeff_X_pow_mul', hH, coeff_mk, ite_t le_rfl, ite_f (by omega), ite_f (by omega),
    Nat.sub_self, coeff_mk, c_eq_choose]
  norm_num

/-- If A ≡ G m coefficientwise mod 3, then [x^m] A^3 ≡ [x^m] (G m)^3 (mod 9). -/
lemma cube_mod9 (A : PowerSeries ℤ) (m : ℕ) (hA : ∀ j, (coeff j A - coeff j (G m)) % 3 = 0) :
    (coeff m (A ^ 3) - coeff m ((G m) ^ 3)) % 9 = 0 := by
  set R : PowerSeries ℤ := PowerSeries.mk (fun j => (coeff j A - coeff j (G m)) / 3) with hR
  have hAR : A = G m + C 3 * R := by
    ext j
    rw [map_add, coeff_C_mul, hR, coeff_mk]
    have := hA j
    omega
  have hC3 : (C (3 : ℤ) : PowerSeries ℤ) = 3 := map_ofNat _ _
  have hC9 : (C (9 : ℤ) : PowerSeries ℤ) = 9 := map_ofNat _ _
  have hexp : A ^ 3 = (G m) ^ 3 + C 9 * ((G m) ^ 2 * R + C 3 * (G m * R ^ 2) + C 3 * R ^ 3) := by
    rw [hAR, hC3, hC9]; ring
  rw [hexp, map_add, coeff_C_mul]
  omega

/-- Coefficientwise construction of the integer cube root. -/
noncomputable def Aseq : ℕ → PowerSeries ℤ
  | 0 => 1
  | k + 1 => Aseq k + C ((b (k + 1) - coeff (k + 1) ((Aseq k) ^ 3)) / 3) * X ^ (k + 1)

lemma coeff_Aseq_succ (k j : ℕ) : coeff j (Aseq (k + 1)) = coeff j (Aseq k) +
    (if j = k + 1 then (b (k + 1) - coeff (k + 1) ((Aseq k) ^ 3)) / 3 else 0) := by
  rw [Aseq, map_add, coeff_C_mul_X_pow]

lemma coeff_zero_Aseq (k : ℕ) : coeff 0 (Aseq k) = 1 := by
  induction k with
  | zero => simp [Aseq]
  | succ k ih => rw [coeff_Aseq_succ, ih, ite_f (by omega), add_zero]

lemma coeff_mul_congr (F F' K K' : PowerSeries ℤ) (n : ℕ)
    (hF : ∀ j ≤ n, coeff j F = coeff j F') (hK : ∀ j ≤ n, coeff j K = coeff j K') :
    ∀ m ≤ n, coeff m (F * K) = coeff m (F' * K') := by
  intro m hm
  rw [coeff_mul, coeff_mul]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  rw [hF p.1 (by omega), hK p.2 (by omega)]

lemma coeff_cube_congr (F F' : PowerSeries ℤ) (n : ℕ)
    (hF : ∀ j ≤ n, coeff j F = coeff j F') : coeff n (F ^ 3) = coeff n (F' ^ 3) := by
  rw [show F ^ 3 = F * F * F by ring, show F' ^ 3 = F' * F' * F' by ring]
  exact coeff_mul_congr _ _ _ _ n (coeff_mul_congr _ _ _ _ n hF hF) hF n le_rfl

lemma Aseq_inv (k : ℕ) : (∀ j, k < j → coeff j (Aseq k) = 0) ∧
    (∀ j ≤ k, coeff j (Aseq k) % 3 = 1) ∧ (∀ j ≤ k, coeff j ((Aseq k) ^ 3) = b j) := by
  induction k with
  | zero =>
    refine ⟨fun j hj => ?_, fun j hj => ?_, fun j hj => ?_⟩
    · simp [Aseq, coeff_one]; omega
    · have : j = 0 := by omega
      subst this; simp [Aseq]
    · have : j = 0 := by omega
      subst this; simp [Aseq, b]
  | succ k ih =>
    obtain ⟨h0, h1, h2⟩ := ih
    set A := Aseq k with hAdef
    set m := k + 1 with hm
    set D := b m - coeff m (A ^ 3) with hD
    have hGm : ∀ j, (coeff j A - coeff j (G m)) % 3 = 0 := by
      intro j
      rw [G, coeff_mk]
      by_cases hj : j ≤ k
      · rw [ite_t (by omega)]; have := h1 j hj; omega
      · rw [ite_f (by omega), h0 j (by omega)]; rfl
    have hc := cube_mod9 A m hGm
    rw [coeff_G3 m (by omega)] at hc
    have hb := b_mod9 m
    have hD9 : D % 9 = 3 := by
      obtain ⟨t, ht⟩ := hb
      omega
    have hAm : coeff m A = 0 := h0 m (by omega)
    refine ⟨fun j hj => ?_, fun j hj => ?_, fun j hj => ?_⟩
    · rw [coeff_Aseq_succ, ← hAdef, h0 j (by omega), ite_f (by omega)]; rfl
    · rw [coeff_Aseq_succ, ← hAdef]
      by_cases hjm : j = m
      · rw [ite_t hjm, hjm, hAm, ← hD]; omega
      · rw [ite_f hjm, add_zero]; exact h1 j (by omega)
    · have hexp : (Aseq (k + 1)) ^ 3 = A ^ 3 + C (3 * (D / 3)) * (X ^ m * A ^ 2) +
          C (3 * (D / 3) ^ 2) * (X ^ (m + m) * A) + C ((D / 3) ^ 3) * X ^ (m + m + m) := by
        rw [Aseq, ← hAdef, ← hD, ← hm]
        simp only [map_mul, map_pow, map_ofNat]
        ring
      have hA2 : coeff 0 (A ^ 2) = 1 := by
        rw [coeff_zero_eq_constantCoeff_apply, map_pow, ← coeff_zero_eq_constantCoeff_apply,
          hAdef, coeff_zero_Aseq, one_pow]
      rw [hexp, map_add, map_add, map_add, coeff_C_mul, coeff_C_mul, coeff_C_mul_X_pow,
        coeff_X_pow_mul', coeff_X_pow_mul']
      have e1 : ¬ (m + m ≤ j) := by omega
      have e2 : j ≠ m + m + m := by omega
      simp only [e1, e2, ↓reduceIte, mul_zero, add_zero]
      by_cases hjm : j = m
      · subst hjm
        simp only [le_refl, ↓reduceIte, Nat.sub_self, hA2]
        omega
      · have e3 : ¬ (m ≤ j) := by omega
        simp only [e3, ↓reduceIte, mul_zero, add_zero]
        exact h2 j (by omega)

/-- The integer cube root of B. -/
noncomputable def Aint : PowerSeries ℤ := PowerSeries.mk (fun n => coeff n (Aseq n))

lemma Aseq_stable (n : ℕ) : ∀ k, n ≤ k → coeff n (Aseq k) = coeff n (Aseq n) := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => rfl
  | succ k hnk ih => rw [coeff_Aseq_succ, ite_f (by omega), add_zero, ih]

theorem Aint_cube : Aint ^ 3 = B := by
  ext n
  rw [coeff_cube_congr Aint (Aseq n) n (fun j hj => by rw [Aint, coeff_mk, Aseq_stable j n hj]),
    (Aseq_inv n).2.2 n le_rfl, B, coeff_mk]

/-- Main theorem about the entry's own definition: if Aq ∈ ℚ⟦X⟧ is the cube root of B with
constant term 1, then each a(n) is an integer, odd iff charSet n. -/
theorem A202943_main (Aq : PowerSeries ℚ) (h3 : Aq ^ 3 = PowerSeries.map (Int.castRingHom ℚ) B)
    (h0 : constantCoeff Aq = 1) (n : ℕ) :
    ∃ z : ℤ, coeff n Aq = z ∧ (Odd z ↔ charSet n) := by
  have hmap : Aq = PowerSeries.map (Int.castRingHom ℚ) Aint := by
    apply cube_root_unique
    · rw [h3, ← map_pow, Aint_cube]
    · exact h0
    · rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, Aint, coeff_mk, coeff_zero_Aseq]; simp
  refine ⟨coeff n Aint, ?_, A202943_conjecture Aint Aint_cube n⟩
  rw [hmap, coeff_map]; rfl
