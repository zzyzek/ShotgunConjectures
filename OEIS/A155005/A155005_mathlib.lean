/-
OEIS A155005: smallest number having exactly n divisors that are contained in its decimal
representation. Conjecture (Robert G. Wilson v, 2009): a(5+5n) = 1125*10^n for n > 0.

Checked here (Lean + Mathlib, no sorry, no native_decide):
* `A121041_1125000`: exactly 19 divisors of 1125000 have their decimal string inside "1125000".
* `A155005_conjecture_false`: the conjecture fails at n = 3 (a(20) is not 1125000).
Reading: "d is contained in the decimal representation of m" means the digit list of d is a
contiguous block of the digit list of m (`List.IsInfix` on `Nat.digits 10`, which lists digits
little-endian; contiguity is unchanged by reversal).
Declarations live in namespace A155005 (left open so the axiom check can name them).
-/
import Mathlib

open scoped Pointwise

namespace A155005

/-- A121041: number of divisors of n whose decimal string occurs in that of n. -/
def A121041 (n : ℕ) : ℕ :=
  ((Nat.divisors n).filter (fun d => Nat.digits 10 d <:+: Nat.digits 10 n)).card

/-- A155005: least m > 0 with A121041(m) = n. -/
noncomputable def a (n : ℕ) : ℕ := sInf {m | 0 < m ∧ A121041 m = n}

/-- Decimal digits with explicit fuel (kernel-friendly). -/
def digF : ℕ → ℕ → List ℕ
  | 0, _ => []
  | f + 1, n => if n = 0 then [] else n % 10 :: digF f (n / 10)

lemma digF_eq : ∀ f n, n < 10 ^ f → digF f n = Nat.digits 10 n
  | 0, n, h => by
    have : n = 0 := by simpa using h
    subst this; simp [digF]
  | f + 1, n, h => by
    by_cases hn : n = 0
    · subst hn; simp [digF]
    · have h' : n / 10 < 10 ^ f := by
        rw [Nat.div_lt_iff_lt_mul (by norm_num)]
        rw [pow_succ] at h
        exact h
      simp only [digF, hn, ite_false]
      rw [Nat.digits_def' (by norm_num) (Nat.pos_of_ne_zero hn), digF_eq f (n / 10) h']

lemma divs : Nat.divisors 1125000 = {1, 2, 3, 4, 5, 6, 8, 9, 10, 12, 15, 18, 20, 24, 25, 30, 36,
    40, 45, 50, 60, 72, 75, 90, 100, 120, 125, 150, 180, 200, 225, 250, 300, 360, 375, 450, 500,
    600, 625, 750, 900, 1000, 1125, 1250, 1500, 1800, 1875, 2250, 2500, 3000, 3125, 3750, 4500,
    5000, 5625, 6250, 7500, 9000, 9375, 11250, 12500, 15000, 15625, 18750, 22500, 25000, 28125,
    31250, 37500, 45000, 46875, 56250, 62500, 75000, 93750, 112500, 125000, 140625, 187500,
    225000, 281250, 375000, 562500, 1125000} := by
  rw [show (1125000 : ℕ) = 8 * 9 * 125 * 125 from rfl, Nat.divisors_mul, Nat.divisors_mul,
    Nat.divisors_mul]
  decide +kernel

theorem A121041_1125000 : A121041 1125000 = 19 := by
  unfold A121041
  have hfil : (Nat.divisors 1125000).filter (fun d => Nat.digits 10 d <:+: Nat.digits 10 1125000) =
      (Nat.divisors 1125000).filter (fun d => digF 8 d <:+: digF 8 1125000) := by
    refine Finset.filter_congr fun d hd => ?_
    have hle : d ≤ 1125000 := Nat.divisor_le hd
    rw [digF_eq 8 d (by omega), digF_eq 8 1125000 (by norm_num)]
  rw [hfil, divs]
  decide +kernel

theorem A155005_conjecture_false : ¬ ∀ n, 0 < n → a (5 + 5 * n) = 1125 * 10 ^ n := by
  intro h
  have h3 : a 20 = 1125000 := by simpa using h 3 (by norm_num)
  have hne : {m | 0 < m ∧ A121041 m = 20}.Nonempty := by
    by_contra hc
    rw [Set.not_nonempty_iff_eq_empty] at hc
    rw [a, hc, Nat.sInf_empty] at h3
    norm_num at h3
  have hm := Nat.sInf_mem hne
  rw [← a, h3] at hm
  have := hm.2
  rw [A121041_1125000] at this
  omega
