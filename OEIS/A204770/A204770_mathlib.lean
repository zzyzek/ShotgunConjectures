import Mathlib
import OpenProblemsLib.PNTApps

/-
OEIS A204770.  Expansion of psi(x^3) * f(-x) in powers of x, psi and f Ramanujan theta functions:
psi(q) = sum_{j ≥ 0} q^(j(j+1)/2) and f(-q) = sum_{k ∈ ℤ} (-1)^k q^(k(3k-1)/2).  Conjecture
(M. Somos): the density of zero terms approaches 1.

Definitions.  `psi3Coeff i` is the coefficient of x^i in psi(x^3) (1 if i = 3 j(j+1)/2, else 0);
`fCoeff l` is the coefficient of x^l in f(-x), the sum of (-1)^k over k ∈ ℤ with
k(3k-1)/2 = l; the search range |k| ≤ l + 1 contains every such k (`fCoeff_range`).
a(n) is the coefficient of x^n in the product of the two series.  The product form
prod (1 - x^k)(1 - x^(6k))/(1 - x^(6k-3)) of the entry (Euler, Gauss) is not used.

Checked here: the conjecture.
* `A204770_sq_add_sq`: a(n) ≠ 0 implies 24 n + 10 = x^2 + y^2 (24 n + 10 = (6k-1)^2 + 9(2j+1)^2).
* `A204770_nonzero_density_zero`: #{n < N : a(n) ≠ 0} / N → 0.  A prime q ≡ 3 (mod 4), q ≠ 3,
  dividing 24 n + 10 exactly once rules out a sum of two squares (Mathlib `Nat.eq_sq_add_sq_iff`);
  the n with no such q have density 0 by `density_zero_of_sieve` of OpenProblemsLib.PNTApps and
  Dirichlet's divergence of the sum of 1/q over q ≡ 3 (mod 4).  Landau's x/sqrt(log x) count is
  not needed.
* `A204770_zero_density_one`: #{n < N : a(n) = 0} / N → 1.
Axioms propext, Classical.choice, Quot.sound.
-/

namespace A204770

open PowerSeries

open Classical in
/-- Coefficient of `x^i` in `psi(x^3) = ∑_{j ≥ 0} x^(3 j (j+1)/2)`. -/
noncomputable def psi3Coeff (i : ℕ) : ℤ :=
  if ∃ j ∈ Finset.range (i + 1), 3 * (j * (j + 1) / 2) = i then 1 else 0

/-- Coefficient of `x^l` in `f(-x) = ∑_{k ∈ ℤ} (-1)^k x^(k(3k-1)/2)`. -/
def fCoeff (l : ℕ) : ℤ :=
  ∑ k ∈ Finset.Icc (-(l : ℤ) - 1) (l + 1), if k * (3 * k - 1) / 2 = l then (-1) ^ k.natAbs else 0

/-- `psi(x^3) f(-x)`. -/
noncomputable def gf : PowerSeries ℤ := PowerSeries.mk psi3Coeff * PowerSeries.mk fCoeff

/-- A204770. -/
noncomputable def a (n : ℕ) : ℤ := coeff n gf

/-- The prime moduli of the sieve. -/
def P : Set ℕ := {q | q.Prime ∧ q % 4 = 3 ∧ q ≠ 3}

/-- `q` divides `24 n + 10` exactly once. -/
def G (q n : ℕ) : Prop := q ∣ 24 * n + 10 ∧ ¬ q ^ 2 ∣ 24 * n + 10

end A204770

open A204770 PowerSeries Filter Topology Finset OpenProblemsLib.PNTApps

/-- The search range in `fCoeff` is complete: `k (3k-1)/2 = l` forces `|k| ≤ l`. -/
theorem fCoeff_range (k : ℤ) (l : ℕ) (h : k * (3 * k - 1) / 2 = l) : -(l : ℤ) - 1 ≤ k ∧ k ≤ l + 1 := by
  have h2 : (2 : ℤ) ∣ k * (3 * k - 1) := by
    rcases Int.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
    · exact ⟨m * (3 * (m + m) - 1), by ring⟩
    · exact ⟨(2 * m + 1) * (3 * m + 1), by ring⟩
  have h3 : k * (3 * k - 1) = 2 * l := by rw [← h]; exact (Int.mul_ediv_cancel' h2).symm
  constructor <;> nlinarith

theorem A204770_sq_add_sq (n : ℕ) (h : a n ≠ 0) : ∃ x y : ℕ, 24 * n + 10 = x ^ 2 + y ^ 2 := by
  unfold a gf at h
  rw [coeff_mul] at h
  obtain ⟨p, hp, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  rw [HasAntidiagonal.mem_antidiagonal] at hp
  simp only [coeff_mk] at hne
  have h1 : psi3Coeff p.1 ≠ 0 := left_ne_zero_of_mul hne
  have h2 : fCoeff p.2 ≠ 0 := right_ne_zero_of_mul hne
  unfold psi3Coeff at h1
  split_ifs at h1 with hj
  · obtain ⟨j, _, hj⟩ := hj
    unfold fCoeff at h2
    obtain ⟨k, _, hk⟩ := Finset.exists_ne_zero_of_sum_ne_zero h2
    split_ifs at hk with hk'
    · have hev : 2 ∣ j * (j + 1) := (Nat.even_mul_succ_self j).two_dvd
      have hA : 2 * (j * (j + 1) / 2) = j * (j + 1) := Nat.mul_div_cancel' hev
      have h2k : (2 : ℤ) ∣ k * (3 * k - 1) := by
        rcases Int.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
        · exact ⟨m * (3 * (m + m) - 1), by ring⟩
        · exact ⟨(2 * m + 1) * (3 * m + 1), by ring⟩
      have hB : 2 * (k * (3 * k - 1) / 2) = k * (3 * k - 1) := Int.mul_ediv_cancel' h2k
      refine ⟨(6 * k - 1).natAbs, 3 * (2 * j + 1), ?_⟩
      zify
      rw [sq_abs]
      have hn : (n : ℤ) = 3 * ((j * (j + 1) / 2 : ℕ) : ℤ) + (k * (3 * k - 1) / 2) := by
        rw [hk', ← hp, ← hj]; push_cast; ring
      have hA' : 2 * ((j * (j + 1) / 2 : ℕ) : ℤ) = (j : ℤ) * (j + 1) := by exact_mod_cast hA
      rw [hn]
      linear_combination 36 * hA' + 12 * hB
    · exact absurd rfl hk
  · exact absurd rfl h1

theorem not_sq_add_sq_of_exact {q m : ℕ} (hq : q.Prime) (hq4 : q % 4 = 3) (h1 : q ∣ m)
    (h2 : ¬ q ^ 2 ∣ m) : ¬ ∃ x y : ℕ, m = x ^ 2 + y ^ 2 := by
  rw [Nat.eq_sq_add_sq_iff]
  intro H
  have hm : m ≠ 0 := by rintro rfl; exact h2 (dvd_zero _)
  have hfact : Fact q.Prime := ⟨hq⟩
  have hev := H q (Nat.mem_primeFactors.mpr ⟨hq, h1, hm⟩) hq4
  have hv1 : 1 ≤ padicValNat q m := (padicValNat_dvd_iff_le hm).mp (by simpa using h1)
  have hv2 : padicValNat q m < 2 := by
    by_contra hc
    exact h2 ((padicValNat_dvd_iff_le hm).mpr (by omega))
  have : padicValNat q m = 1 := by omega
  rw [this] at hev
  exact Nat.not_even_one hev

open Classical in
/-- At least `q - 1` residues `n mod q^2` have `q` dividing `24 n + 10` exactly once. -/
theorem count_G (q : ℕ) (hq : q ∈ P) : q - 1 ≤ Nat.count (G q) (q ^ 2) := by
  obtain ⟨hqp, hq4, hq3⟩ := hq
  have hq2 : q ≠ 2 := by rintro rfl; norm_num at hq4
  have hqpos := hqp.pos
  have : NeZero (q ^ 2) := ⟨by positivity⟩
  have hcop : Nat.Coprime 24 (q ^ 2) := by
    refine Nat.Coprime.pow_right 2 ?_
    rw [Nat.coprime_comm, hqp.coprime_iff_not_dvd]
    intro hd
    have h24 : (24 : ℕ) = 2 ^ 3 * 3 := by norm_num
    rw [h24] at hd
    rcases (Nat.Prime.dvd_mul hqp).mp hd with h | h
    · exact hq2 ((Nat.prime_dvd_prime_iff_eq hqp Nat.prime_two).mp (hqp.dvd_of_dvd_pow h))
    · exact hq3 ((Nat.prime_dvd_prime_iff_eq hqp Nat.prime_three).mp h)
  set u := ZMod.unitOfCoprime 24 hcop
  set f : ℕ → ℕ := fun j => ((((q * j : ℕ) : ZMod (q ^ 2)) - 10) * (u⁻¹ : (ZMod (q ^ 2))ˣ)).val
  have hf : ∀ j, ((24 * f j + 10 : ℕ) : ZMod (q ^ 2)) = ((q * j : ℕ) : ZMod (q ^ 2)) := by
    intro j
    simp only [f]
    push_cast
    rw [ZMod.natCast_zmod_val]
    have hu : (24 : ZMod (q ^ 2)) = (u : ZMod (q ^ 2)) := by
      simp [u, ZMod.coe_unitOfCoprime]
    rw [hu, ← mul_assoc, mul_comm (u : ZMod (q ^ 2)), mul_assoc, Units.mul_inv, mul_one]
    ring
  have hmod : ∀ j, 24 * f j + 10 ≡ q * j [MOD q ^ 2] := fun j =>
    (ZMod.natCast_eq_natCast_iff _ _ _).mp (hf j)
  rw [Nat.count_eq_card_filter_range]
  have hcard : (Finset.Ico 1 q).card = q - 1 := by simp
  rw [← hcard]
  refine Finset.card_le_card_of_injOn f ?_ ?_
  · intro j hj
    simp only [coe_Ico, Set.mem_Ico] at hj
    simp only [coe_filter, mem_range, Set.mem_ofPred_eq]
    refine ⟨ZMod.val_lt _, ?_, ?_⟩
    · rw [(hmod j).dvd_iff (dvd_pow_self q two_ne_zero)]
      exact dvd_mul_right q j
    · rw [(hmod j).dvd_iff dvd_rfl, sq]
      intro hd
      have := Nat.le_of_dvd (by omega) (Nat.dvd_of_mul_dvd_mul_left hqpos hd)
      omega
  · intro j hj j' hj' hjj
    simp only [coe_Ico, Set.mem_Ico] at hj hj'
    have e1 : q * j ≡ q * j' [MOD q ^ 2] :=
      (hmod j).symm.trans (by rw [show f j = f j' from hjj]; exact hmod j')
    unfold Nat.ModEq at e1
    rw [Nat.mod_eq_of_lt (by rw [sq]; exact Nat.mul_lt_mul_of_pos_left hj.2 hqpos),
      Nat.mod_eq_of_lt (by rw [sq]; exact Nat.mul_lt_mul_of_pos_left hj'.2 hqpos)] at e1
    exact Nat.eq_of_mul_eq_mul_left hqpos e1

open Classical in
theorem A204770_nonzero_density_zero :
    Tendsto (fun N : ℕ => (Nat.count (fun n => a n ≠ 0) N : ℝ) / N) atTop (𝓝 0) := by
  have hsieve : Tendsto (fun N : ℕ => (Nat.count (fun n => ∀ q ∈ P, ¬ G q n) N : ℝ) / N) atTop
      (𝓝 0) := by
    refine density_zero_of_sieve P (fun q hq => hq.1) ?_ G ?_ count_G
    · intro hS
      apply not_summable_one_div_prime_mod (q := 4) (a := 3) (by norm_num) (by norm_num)
      have h3 : Summable (fun n : ℕ => if n = 3 then (1 : ℝ) / 3 else 0) :=
        summable_of_ne_finset_zero (s := {3}) fun n hn => by
          simp only [Finset.mem_singleton] at hn; simp [hn]
      refine (hS.add h3).congr fun n => ?_
      by_cases hn : n = 3
      · subst hn; norm_num [P]
      · by_cases hp : n.Prime ∧ n % 4 = 3
        · have : n ∈ P := ⟨hp.1, hp.2, hn⟩
          simp [this, hn, hp]
        · have : n ∉ P := fun h => hp ⟨h.1, h.2.1⟩
          simp [this, hn, hp]
    · intro q hq n
      have hm : 24 * n + 10 ≡ 24 * (n % q ^ 2) + 10 [MOD q ^ 2] :=
        ((Nat.mod_modEq n (q ^ 2)).symm.mul_left 24).add_right 10
      simp only [G, hm.dvd_iff (dvd_pow_self q two_ne_zero), hm.dvd_iff dvd_rfl]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsieve
    (fun N => by positivity) (fun N => ?_)
  have hle : Nat.count (fun n => a n ≠ 0) N ≤ Nat.count (fun n => ∀ q ∈ P, ¬ G q n) N := by
    refine Nat.count_mono_left fun n _ hn q hq hG => ?_
    obtain ⟨x, y, hxy⟩ := A204770_sq_add_sq n hn
    exact not_sq_add_sq_of_exact hq.1 hq.2.1 hG.1 hG.2 ⟨x, y, hxy⟩
  have hR : (Nat.count (fun n => a n ≠ 0) N : ℝ) ≤
      (Nat.count (fun n => ∀ q ∈ P, ¬ G q n) N : ℝ) := by exact_mod_cast hle
  exact div_le_div_of_nonneg_right hR (Nat.cast_nonneg _)

open Classical in
/-- Somos's conjecture: the density of zero terms is 1. -/
theorem A204770_zero_density_one :
    Tendsto (fun N : ℕ => (Nat.count (fun n => a n = 0) N : ℝ) / N) atTop (𝓝 1) := by
  have h := A204770_nonzero_density_zero
  have h1 : Tendsto (fun N : ℕ => (1 : ℝ) - (Nat.count (fun n => a n ≠ 0) N : ℝ) / N) atTop
      (𝓝 1) := by simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub h
  refine h1.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with N hN
  have hsum : Nat.count (fun n => a n = 0) N + Nat.count (fun n => a n ≠ 0) N = N := by
    simp only [Nat.count_eq_card_filter_range]
    rw [Finset.card_filter_add_card_filter_not, Finset.card_range]
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have : (Nat.count (fun n => a n = 0) N : ℝ) = N - Nat.count (fun n => a n ≠ 0) N := by
    have := congrArg (fun t : ℕ => (t : ℝ)) hsum
    push_cast at this; linarith
  rw [this]; field_simp
