import Mathlib

/-
OEIS A179873: values of the antiharmonic mean B(h) = Σ k² / Σ k over 1 ≤ k ≤ h with
gcd(k, h) = 1, for the h with B(h) an integer (A179871), in order of h.
Conjecture: nondecreasing sequence of odd numbers.
OEIS A179874: the possible values of A179873 in increasing order. Conjecture: all odd.

Main theorems.
* `B_odd h t : 1 ≤ h → B h = t → Odd t` (both conjectures' oddness).
* `B_mono : 1 ≤ h ≤ h' → B h = t → B h' = t' → t ≤ t'` (A179873 nondecreasing).
* `three_B`: B h = t ∈ ℤ → 3t = 2h ± 1.
Route.
* `sum_moebius_mul_self`: Σ_{d | n} μ(d) d = Π_{p | n} (1 - p) (multiplicative functions).
* `G_eq`, `inversion`: Σ_{k < n} k^r = Σ_{d | n} d^r F_r(n/d), Möbius inversion.
* `F_one`, `F_two`: Σ_{units} k = n φ(n)/2, Σ_{units} k² = (2n²φ(n) + n Π(1-p))/6 (n ≥ 2).
* `B_formula`: 3φ(h) B(h) = 2hφ(h) + Π(1-p); then φ(h) Π p = h Π (p-1) forces h squarefree.
Checked: all of the above.  Not checked: agreement with the OEIS data (certificate/check.py).
-/

namespace OEIS_A179874

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta ArithmeticFunction.omega

/-- Σ_{d | n} μ(d) d = Π_{p | n} (1 - p). -/
theorem sum_moebius_mul_self (n : ℕ) (hn : n ≠ 0) :
    ∑ d ∈ n.divisors, (μ d : ℤ) * d = ∏ p ∈ n.primeFactors, (1 - (p : ℤ)) := by
  let f : ArithmeticFunction ℤ := (pmul (μ : ArithmeticFunction ℤ) (ArithmeticFunction.id : ArithmeticFunction ℤ)) * ζ
  have hf : f.IsMultiplicative :=
    (isMultiplicative_moebius.intCast.pmul isMultiplicative_id.natCast).mul isMultiplicative_zeta.natCast
  have hg := IsMultiplicative.prodPrimeFactors (fun p : ℕ => 1 - (p : ℤ))
  have heq : f = prodPrimeFactors (fun p : ℕ => 1 - (p : ℤ)) := by
    rw [IsMultiplicative.eq_iff_eq_on_prime_powers f hf _ hg]
    intro p i hp
    rw [prodPrimeFactors_apply (pow_ne_zero _ hp.ne_zero)]
    simp only [f, coe_mul_zeta_apply, pmul_apply, natCoe_apply, id_apply]
    rw [Nat.divisors_prime_pow hp, Finset.sum_map]
    rcases i with _ | i
    · simp
    · rw [Nat.primeFactors_prime_pow (Nat.succ_ne_zero i) hp, Finset.prod_singleton]
      rw [Finset.sum_range_succ', Finset.sum_range_succ']
      have h0 : ∀ j ∈ range i, (μ (p ^ (j + 1 + 1)) : ℤ) * ((p ^ (j + 1 + 1) : ℕ) : ℤ) = 0 := by
        intro j _
        rw [moebius_apply_prime_pow hp (by omega)]
        simp
      simp only [Function.Embedding.coeFn_mk] at h0 ⊢
      rw [Finset.sum_congr rfl h0]
      simp [moebius_apply_prime hp]
      ring
  have := congrArg (fun F : ArithmeticFunction ℤ => F n) heq
  simp only [f, coe_mul_zeta_apply, pmul_apply, natCoe_apply, id_apply,
    prodPrimeFactors_apply hn] at this
  exact this

/-- Σ_{j < m, gcd(m, j) = 1} j^r. -/
def F (r m : ℕ) : ℚ := ∑ j ∈ (range m).filter (fun j => m.gcd j = 1), (j : ℚ) ^ r

/-- Σ_{k < b} k^r. -/
def G (r b : ℕ) : ℚ := ∑ k ∈ range b, (k : ℚ) ^ r

theorem fiber_sum (r n d : ℕ) (hd : d ∣ n) (hn : 0 < n) :
    ∑ k ∈ (range n).filter (fun k => n.gcd k = d), (k : ℚ) ^ r = (d : ℚ) ^ r * F r (n / d) := by
  obtain ⟨x, rfl⟩ := hd
  have hd0 : 0 < d := Nat.pos_of_mul_pos_right hn
  rw [Nat.mul_div_cancel_left x hd0, F, Finset.mul_sum]
  symm
  apply Finset.sum_bij (fun j _ => d * j)
  · simp only [mem_filter, mem_range]
    intro a ha
    refine ⟨by nlinarith [ha.1], ?_⟩
    rw [Nat.gcd_mul_left, ha.2, mul_one]
  · intro a _ b _ h
    exact Nat.eq_of_mul_eq_mul_left hd0 h
  · simp only [mem_filter, mem_range, exists_prop]
    intro b hb
    have : d ∣ b := by rw [← hb.2]; exact Nat.gcd_dvd_right _ _
    obtain ⟨q, rfl⟩ := this
    refine ⟨q, ⟨?_, ?_⟩, rfl⟩
    · exact (Nat.mul_lt_mul_left hd0).1 hb.1
    · have h2 := hb.2
      rwa [Nat.gcd_mul_left, mul_eq_left₀ hd0.ne'] at h2
  · intro a _
    push_cast; ring

theorem G_eq (r n : ℕ) (hn : 0 < n) : G r n = ∑ d ∈ n.divisors, (d : ℚ) ^ r * F r (n / d) := by
  unfold G
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun k => n.gcd k) (t := n.divisors)]
  · exact Finset.sum_congr rfl (fun d hd => fiber_sum r n d (Nat.dvd_of_mem_divisors hd) hn)
  · intro k _
    simp only [Nat.mem_divisors]
    exact ⟨Nat.gcd_dvd_left _ _, hn.ne'⟩

theorem inversion (r n : ℕ) (hn : 0 < n) :
    ∑ x ∈ n.divisorsAntidiagonal, (μ x.1 : ℚ) * (G r x.2 / (x.2 : ℚ) ^ r) = F r n / (n : ℚ) ^ r := by
  have h := (sum_eq_iff_sum_smul_moebius_eq (f := fun i => F r i / (i : ℚ) ^ r)
    (g := fun b => G r b / (b : ℚ) ^ r)).mp (by
      intro m hm
      rw [G_eq r m hm, Finset.sum_div, ← Nat.sum_div_divisors m (fun i => F r i / (i : ℚ) ^ r)]
      apply Finset.sum_congr rfl
      intro d hd
      have hdm := Nat.dvd_of_mem_divisors hd
      have hd0 : (d : ℚ) ≠ 0 := by
        have := Nat.pos_of_mem_divisors hd; exact_mod_cast this.ne'
      have hq : ((m / d : ℕ) : ℚ) = (m : ℚ) / d := Nat.cast_div hdm hd0
      rw [hq]
      have hm0 : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
      field_simp
      rw [mul_assoc, ← mul_pow, div_mul_cancel₀ _ hd0]) n hn
  simpa [zsmul_eq_mul] using h

theorem G_one (b : ℕ) : G 1 b * 2 = (b : ℚ) * (b - 1) := by
  induction b with
  | zero => simp [G]
  | succ b ih =>
    unfold G at ih ⊢
    rw [Finset.sum_range_succ, add_mul, ih]
    push_cast; ring

theorem G_two (b : ℕ) : G 2 b * 6 = ((b : ℚ) - 1) * b * (2 * b - 1) := by
  induction b with
  | zero => simp [G]
  | succ b ih =>
    unfold G at ih ⊢
    rw [Finset.sum_range_succ, add_mul, ih]
    push_cast; ring

theorem S0 (n : ℕ) (hn : 0 < n) :
    ∑ x ∈ n.divisorsAntidiagonal, (μ x.1 : ℚ) = if n = 1 then 1 else 0 := by
  have h := (sum_eq_iff_sum_smul_moebius_eq (R := ℚ) (f := fun i => if i = 1 then (1 : ℚ) else 0)
    (g := fun _ => (1 : ℚ))).mp (by
      intro m hm
      rw [Finset.sum_ite_eq' m.divisors 1]
      simp [Nat.one_mem_divisors.mpr hm.ne']) n hn
  simpa [zsmul_eq_mul] using h

theorem S1 (n : ℕ) (hn : 0 < n) :
    ∑ x ∈ n.divisorsAntidiagonal, (μ x.1 : ℚ) * x.2 = (n.totient : ℚ) := by
  have h := (sum_eq_iff_sum_smul_moebius_eq (R := ℚ) (f := fun i => (i.totient : ℚ))
    (g := fun b => (b : ℚ))).mp (by
      intro m _
      have := Nat.sum_totient m
      exact_mod_cast this) n hn
  simpa [zsmul_eq_mul] using h

theorem Sm (n : ℕ) (hn : 0 < n) :
    ∑ x ∈ n.divisorsAntidiagonal, (μ x.1 : ℚ) * x.1 = ((∏ p ∈ n.primeFactors, (1 - (p : ℤ)) : ℤ) : ℚ) := by
  rw [← sum_moebius_mul_self n hn.ne']
  push_cast
  rw [Nat.sum_divisorsAntidiagonal (fun a _ => (μ a : ℚ) * a)]

theorem F_one (n : ℕ) (hn : 2 ≤ n) : F 1 n * 2 = n * n.totient := by
  have hn0 : 0 < n := by omega
  have h := inversion 1 n hn0
  have hn1 : (n : ℚ) ≠ 0 := by exact_mod_cast hn0.ne'
  have e : ∀ x ∈ n.divisorsAntidiagonal, (μ x.1 : ℚ) * (G 1 x.2 / (x.2 : ℚ) ^ 1) =
      (μ x.1 : ℚ) * x.2 / 2 - (μ x.1 : ℚ) / 2 := by
    intro x hx
    have hx2 : (x.2 : ℚ) ≠ 0 := by
      have := (Nat.mem_divisorsAntidiagonal.mp hx).1
      have : x.2 ≠ 0 := fun h0 => by rw [h0, mul_zero] at this; omega
      exact_mod_cast this
    have := G_one x.2
    field_simp
    linear_combination (μ x.1 : ℚ) * this
  have hS0 : ∑ x ∈ n.divisorsAntidiagonal, (μ x.1 : ℚ) = 0 := by
    rw [S0 n hn0]; simp; omega
  rw [Finset.sum_congr rfl e, Finset.sum_sub_distrib, ← Finset.sum_div, ← Finset.sum_div,
    S1 n hn0, hS0] at h
  field_simp at h
  linear_combination -h

/-- T(n) = Π_{p | n} (1 - p). -/
def T (n : ℕ) : ℤ := ∏ p ∈ n.primeFactors, (1 - (p : ℤ))

theorem F_two (n : ℕ) (hn : 2 ≤ n) : F 2 n * 6 = 2 * (n : ℚ) ^ 2 * n.totient + n * T n := by
  have hn0 : 0 < n := by omega
  have h := inversion 2 n hn0
  have hn1 : (n : ℚ) ≠ 0 := by exact_mod_cast hn0.ne'
  have e : ∀ x ∈ n.divisorsAntidiagonal, (μ x.1 : ℚ) * (G 2 x.2 / (x.2 : ℚ) ^ 2) =
      (μ x.1 : ℚ) * x.2 / 3 - (μ x.1 : ℚ) / 2 + (μ x.1 : ℚ) * x.1 / (6 * n) := by
    intro x hx
    have hprod := (Nat.mem_divisorsAntidiagonal.mp hx).1
    have hx2 : (x.2 : ℚ) ≠ 0 := by
      have : x.2 ≠ 0 := fun h0 => by rw [h0, mul_zero] at hprod; omega
      exact_mod_cast this
    have hx1 : (x.1 : ℚ) ≠ 0 := by
      have : x.1 ≠ 0 := fun h0 => by rw [h0, zero_mul] at hprod; omega
      exact_mod_cast this
    have hq : (x.1 : ℚ) * x.2 = n := by exact_mod_cast hprod
    have hG : G 2 x.2 = ((x.2 : ℚ) - 1) * x.2 * (2 * x.2 - 1) / 6 := by
      have := G_two x.2; linarith
    rw [hG, ← hq]
    field_simp
    ring
  have hS0 : ∑ x ∈ n.divisorsAntidiagonal, (μ x.1 : ℚ) = 0 := by
    rw [S0 n hn0]; simp; omega
  rw [Finset.sum_congr rfl e, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_div,
    ← Finset.sum_div, ← Finset.sum_div, S1 n hn0, hS0, Sm n hn0] at h
  unfold T
  field_simp at h
  linear_combination (-1 / 6 : ℚ) * h

/-- The numbers 1 ≤ k ≤ h coprime to h. -/
def cop (h : ℕ) : Finset ℕ := (Icc 1 h).filter (fun k => Nat.Coprime k h)

/-- Antiharmonic mean B(h) = Σ k² / Σ k over k ∈ cop h (A175505/A175506; A179873 lists the
integral values in order of h, A179871 the h). -/
def B (h : ℕ) : ℚ := (∑ k ∈ cop h, (k : ℚ) ^ 2) / (∑ k ∈ cop h, (k : ℚ))

theorem cop_eq (h : ℕ) (hh : 2 ≤ h) : cop h = (range h).filter (fun j => h.gcd j = 1) := by
  ext k
  simp only [cop, mem_filter, mem_Icc, mem_range, Nat.Coprime]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨?_, by rw [Nat.gcd_comm]; exact h3⟩
    rcases Nat.lt_or_ge k h with hlt | hge
    · exact hlt
    · have : k = h := by omega
      subst this; rw [Nat.gcd_self] at h3; omega
  · rintro ⟨h1, h2⟩
    refine ⟨⟨?_, by omega⟩, by rw [Nat.gcd_comm]; exact h2⟩
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · rw [Nat.gcd_zero_right] at h2; omega
    · exact hk

theorem B_formula (h : ℕ) (hh : 2 ≤ h) :
    B h * (3 * h.totient) = 2 * h * h.totient + T h := by
  have h1 := F_one h hh
  have h2 := F_two h hh
  have hF1 : (∑ k ∈ cop h, (k : ℚ)) = F 1 h := by rw [cop_eq h hh]; simp [F]
  have hF2 : (∑ k ∈ cop h, (k : ℚ) ^ 2) = F 2 h := by rw [cop_eq h hh]; rfl
  have hphi : (h.totient : ℚ) ≠ 0 := by
    have : 0 < h.totient := Nat.totient_pos.mpr (by omega)
    exact_mod_cast this.ne'
  have hh0 : (h : ℚ) ≠ 0 := by exact_mod_cast (show h ≠ 0 by omega)
  unfold B
  rw [hF1, hF2]
  have hF1' : F 1 h = h * h.totient / 2 := by linarith
  have hF2' : F 2 h = (2 * (h : ℚ) ^ 2 * h.totient + h * T h) / 6 := by linarith
  rw [hF1', hF2']
  field_simp
  ring

theorem T_eq (h : ℕ) :
    T h = (-1) ^ h.primeFactors.card * ((∏ p ∈ h.primeFactors, (p - 1) : ℕ) : ℤ) := by
  unfold T
  push_cast
  rw [← Finset.prod_const, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  have : 1 ≤ p := (Nat.prime_of_mem_primeFactors hp).one_lt.le
  push_cast [this]
  ring

/-- If B(h) is an integer t (h ≥ 1) then 3t = 2h + 1 or 3t = 2h - 1. -/
theorem three_B (h : ℕ) (hh : 1 ≤ h) (t : ℤ) (hB : B h = t) :
    3 * t = 2 * h + 1 ∨ 3 * t = 2 * h - 1 := by
  rcases Nat.lt_or_ge h 2 with h1 | h2
  · obtain rfl : h = 1 := by omega
    have : B 1 = 1 := by
      unfold B cop
      rw [show (Icc 1 1).filter (fun k => Nat.Coprime k 1) = {1} by decide]
      simp
    rw [this] at hB
    left; have : t = 1 := by exact_mod_cast hB.symm
    subst this; norm_num
  · have hf := B_formula h h2
    rw [hB, T_eq] at hf
    set c := h.primeFactors.card
    set Q := ∏ p ∈ h.primeFactors, (p - 1)
    set φh := h.totient
    have hphi : 0 < φh := Nat.totient_pos.mpr (by omega)
    have hz : (t : ℤ) * (3 * φh) = 2 * h * φh + (-1) ^ c * (Q : ℤ) := by exact_mod_cast hf
    have hsign : ((-1 : ℤ) ^ c) * (-1) ^ c = 1 := by rw [← mul_pow]; norm_num
    have hdvdZ : (φh : ℤ) ∣ (Q : ℤ) := by
      refine ⟨(-1) ^ c * (3 * t - 2 * h), ?_⟩
      linear_combination (-(-1 : ℤ) ^ c) * hz - (Q : ℤ) * hsign
    have hdvd : φh ∣ Q := Int.natCast_dvd_natCast.mp hdvdZ
    obtain ⟨c', hc'⟩ := hdvd
    have hmul : φh * (∏ p ∈ h.primeFactors, p) = h * Q := Nat.totient_mul_prod_primeFactors h
    have hP := Nat.prod_primeFactors_dvd h
    have hQpos : 0 < Q := Finset.prod_pos (fun p hp => by
      have := (Nat.prime_of_mem_primeFactors hp).two_le; omega)
    have hPle : ∏ p ∈ h.primeFactors, p ≤ h := Nat.le_of_dvd (by omega) hP
    rw [hc'] at hmul hQpos
    have hc1 : h * c' = ∏ p ∈ h.primeFactors, p := by
      have : φh * (h * c') = φh * ∏ p ∈ h.primeFactors, p := by rw [hmul]; ring
      exact Nat.eq_of_mul_eq_mul_left hphi this
    have hc'1 : c' = 1 := by
      have hc0 : 0 < c' := Nat.pos_of_mul_pos_left hQpos
      have : h * c' ≤ h * 1 := by rw [hc1]; omega
      have := Nat.le_of_mul_le_mul_left this (by omega)
      omega
    rw [hc'1, mul_one] at hc'
    rw [hc'] at hz
    have hphiZ : (φh : ℤ) ≠ 0 := by exact_mod_cast hphi.ne'
    have h3 : 3 * t = 2 * h + (-1) ^ c := by
      apply mul_right_cancel₀ hphiZ
      linear_combination hz
    rcases neg_one_pow_eq_or ℤ c with h4 | h4
    · left; rw [h3, h4]
    · right; rw [h3, h4]; ring

/-- A179873 / A179874: every integral antiharmonic mean B(h) is odd. -/
theorem B_odd (h : ℕ) (hh : 1 ≤ h) (t : ℤ) (hB : B h = t) : Odd t := by
  rw [Int.odd_iff]
  rcases three_B h hh t hB with h1 | h1 <;> omega

/-- A179873: the integral values B(h), listed in increasing order of h, are nondecreasing. -/
theorem B_mono (h h' : ℕ) (hh : 1 ≤ h) (hle : h ≤ h') (t t' : ℤ) (hB : B h = t) (hB' : B h' = t') :
    t ≤ t' := by
  rcases Nat.eq_or_lt_of_le hle with rfl | hlt
  · have : (t : ℚ) = t' := by rw [← hB, ← hB']
    exact_mod_cast this.le
  · rcases three_B h hh t hB with h1 | h1 <;> rcases three_B h' (by omega) t' hB' with h2 | h2 <;> omega

end OEIS_A179874

open OEIS_A179874
