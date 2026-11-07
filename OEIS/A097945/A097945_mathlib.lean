import Mathlib
import PNTPlus.Consequences

/-
OEIS A097945: a(n) = mu(n) * phi(n).
Conjecture (entry, G. McGarvey): Sum_{n>=1} mu(n)/phi(n) = Sum_{n>=1} a(n)/phi(n)^2 = 0,
and Sum_{n>=1} mu(n)/phi(n)^z = 0 for Re(z) > 1.

Main theorems.
* `A097945_re_gt_one`: for every complex z with Re z > 1 the series
  Sum mu(n)/phi(n)^z is absolutely summable with sum 0 (unconditional).
* `A097945_conditional`: if Sum_{n<=N} mu(n)/n -> 0 (Landau's form of the prime
  number theorem), then the partial sums Sum_{n<=N} mu(n)/phi(n) and
  Sum_{n<=N} a(n)/phi(n)^2 tend to 0.
* `sum_mu_div_tendsto`: Sum_{n<=N} mu(n)/n -> 0, from `mu_pnt_alt` of the vendored
  PrimeNumberTheoremAnd library (lib/PNTPlus, rev 127b50e3).
* `A097945_s_one`: the s = 1 statement, unconditional.

Route.
* `summable_of_mult`: a nonnegative multiplicative F with
  Sum_e F(p^e) <= 1 + c(p), c summable, is summable (partial sums are bounded
  by the Euler product over smooth numbers, EulerProduct in Mathlib).
* Re z > 1: Euler product (`EulerProduct.eulerProduct_hasProd`); the factor at
  p = 2 is 1 - 1/phi(2)^z = 0, so the sum is 0.
* s = 1: mu/phi = k * (mu/id) (Dirichlet convolution) with k = (mu/phi) * (1/id),
  |k(p^e)| = 1/((p-1) p^e), so Sum |k| < infinity; then
  Sum_{n<=N} mu(n)/phi(n) = Sum_{d<=N} k(d) A(N/d), A(M) = Sum_{m<=M} mu(m)/m,
  and Tannery's theorem (`tendsto_tsum_of_dominated_convergence`).

The hypothesis Sum mu(n)/n = 0 (von Mangoldt 1897 / Landau 1899) is not in Mathlib
at the revision used; it comes from `mu_pnt_alt` in lib/PNTPlus (vendored
PrimeNumberTheoremAnd), compiled with this repo's tools/buildlib.sh.
Not checked in this file: that the Lean statements match the OEIS text.
-/

open ArithmeticFunction Finset Filter Topology
open scoped ArithmeticFunction.zeta ArithmeticFunction.Moebius

namespace A097945

/-- OEIS A097945. -/
def a (n : ℕ) : ℤ := moebius n * (n.totient : ℤ)

/-- A nonnegative multiplicative function whose prime-power sums are at most
`1 + c p`, with `c` summable, is summable. -/
theorem summable_of_mult (F : ℕ → ℝ) (c : ℕ → ℝ)
    (h0 : F 0 = 0) (h1 : F 1 = 1)
    (hmul : ∀ {m n : ℕ}, Nat.Coprime m n → F (m * n) = F m * F n)
    (hnn : ∀ n, 0 ≤ F n)
    (hpp : ∀ {p : ℕ}, p.Prime → Summable (fun e : ℕ => F (p ^ e)))
    (hc : Summable c) (hc0 : ∀ n, 0 ≤ c n)
    (hle : ∀ {p : ℕ}, p.Prime → ∑' e, F (p ^ e) ≤ 1 + c p) : Summable F := by
  refine summable_of_sum_range_le hnn (c := Real.exp (∑' n, c n)) (fun N => ?_)
  have hpp' : ∀ {p : ℕ}, p.Prime → Summable (fun e : ℕ => ‖F (p ^ e)‖) := by
    intro p hp
    simpa [Real.norm_eq_abs, abs_of_nonneg (hnn _)] using hpp hp
  obtain ⟨-, hH⟩ :=
    EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum
      (f := F) h1 hmul hpp' N
  replace hH : HasSum (N.smoothNumbers.indicator F) _ := hasSum_subtype_iff_indicator.mp hH
  have h1' : ∑ i ∈ range N, F i = ∑ i ∈ range N, (N.smoothNumbers).indicator F i := by
    refine sum_congr rfl (fun i hi => ?_)
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · rw [Set.indicator_apply]
      split_ifs <;> simp [h0]
    · rw [Set.indicator_of_mem]
      exact Nat.mem_smoothNumbers_of_lt hi0 (mem_range.mp hi)
  have h2 : ∑ i ∈ range N, (N.smoothNumbers).indicator F i ≤
      ∏ p ∈ N.primesBelow, ∑' e : ℕ, F (p ^ e) :=
    sum_le_hasSum _ (fun i _ => Set.indicator_nonneg (fun j _ => hnn j) i) hH
  have h3 : ∏ p ∈ N.primesBelow, ∑' e : ℕ, F (p ^ e) ≤ ∏ p ∈ N.primesBelow, Real.exp (c p) := by
    refine prod_le_prod₀ (fun p _ => tsum_nonneg (fun e => hnn _)) (fun p hp => ?_)
    have hp' : p.Prime := (Nat.mem_primesBelow.mp hp).2
    calc ∑' e : ℕ, F (p ^ e) ≤ 1 + c p := hle hp'
      _ ≤ Real.exp (c p) := by linarith [Real.add_one_le_exp (c p)]
  have h4 : ∏ p ∈ N.primesBelow, Real.exp (c p) ≤ Real.exp (∑' n, c n) := by
    rw [← Real.exp_sum]
    exact Real.exp_le_exp.mpr (hc.sum_le_tsum _ (fun i _ => hc0 i))
  linarith

/-! Part 1: Re z > 1. -/

/-- The summand mu(n)/phi(n)^z. -/
noncomputable def fz (z : ℂ) (n : ℕ) : ℂ := (moebius n : ℂ) / ((n.totient : ℂ) ^ z)

theorem fz_mul (z : ℂ) {m n : ℕ} (h : Nat.Coprime m n) : fz z (m * n) = fz z m * fz z n := by
  simp only [fz, Nat.totient_mul h, isMultiplicative_moebius.map_mul_of_coprime h, Nat.cast_mul,
    Int.cast_mul, Complex.natCast_mul_natCast_cpow]
  rw [mul_div_mul_comm]

theorem fz_one (z : ℂ) : fz z 1 = 1 := by simp [fz]

theorem fz_zero (z : ℂ) : fz z 0 = 0 := by simp [fz]

/-- The norm of the summand. -/
noncomputable def Fz (σ : ℝ) (n : ℕ) : ℝ := |(moebius n : ℝ)| / ((n.totient : ℝ) ^ σ)

theorem norm_fz (z : ℂ) (n : ℕ) : ‖fz z n‖ = Fz z.re n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [fz, Fz]
  · have ht : 0 < n.totient := Nat.totient_pos.mpr hn
    rw [fz, Fz, norm_div, Complex.norm_natCast_cpow_of_pos ht]
    simp [Complex.norm_intCast]

theorem moebius_prime_pow_ge_two {p e : ℕ} (hp : p.Prime) (he : 2 ≤ e) : moebius (p ^ e) = 0 := by
  rw [moebius_apply_prime_pow hp (by omega)]
  simp; omega

theorem Fz_prime_pow (σ : ℝ) {p : ℕ} (hp : p.Prime) (e : ℕ) :
    Fz σ (p ^ e) = if e = 0 then 1 else if e = 1 then 1 / ((p : ℝ) - 1) ^ σ else 0 := by
  rcases Nat.lt_trichotomy e 1 with h | rfl | h
  · obtain rfl : e = 0 := by omega
    simp [Fz]
  · simp [Fz, moebius_apply_prime hp, Nat.totient_prime hp, Nat.cast_sub hp.one_le]
  · rw [Fz, moebius_prime_pow_ge_two hp (by omega)]
    split_ifs <;> first | omega | simp

theorem Fz_prime_pow_ge_two (σ : ℝ) {p e : ℕ} (hp : p.Prime) (he : 2 ≤ e) : Fz σ (p ^ e) = 0 := by
  rw [Fz, moebius_prime_pow_ge_two hp he]
  simp

/-- c(n) = 1/(n-1)^σ for n >= 2. -/
noncomputable def cS (σ : ℝ) (n : ℕ) : ℝ := if 2 ≤ n then 1 / ((n : ℝ) - 1) ^ σ else 0

theorem summable_cS {σ : ℝ} (hσ : 1 < σ) : Summable (cS σ) := by
  rw [← summable_nat_add_iff 2]
  have h := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_rpow.mpr hσ)
  refine h.congr (fun n => ?_)
  simp only [cS, show 2 ≤ n + 2 by omega, ite_true]
  push_cast
  ring_nf

theorem cS_nonneg {σ : ℝ} (n : ℕ) : 0 ≤ cS σ n := by
  unfold cS
  split_ifs with h
  · have : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
    positivity
  · rfl

theorem summable_Fz {σ : ℝ} (hσ : 1 < σ) : Summable (Fz σ) := by
  refine summable_of_mult (Fz σ) (cS σ) (by simp [Fz]) (by simp [Fz]) ?_ ?_ ?_
    (summable_cS hσ) cS_nonneg ?_
  · intro m n h
    simp only [Fz, Nat.totient_mul h, isMultiplicative_moebius.map_mul_of_coprime h,
      Int.cast_mul, abs_mul, Nat.cast_mul]
    rw [Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _), mul_div_mul_comm]
  · intro n
    unfold Fz
    positivity
  · intro p hp
    refine summable_of_ne_finset_zero (s := range 2) (fun e he => ?_)
    exact Fz_prime_pow_ge_two σ hp (by simp at he; omega)
  · intro p hp
    rw [tsum_eq_sum (s := range 2) (fun e he =>
      Fz_prime_pow_ge_two σ hp (by simp at he; omega))]
    simp [Fz_prime_pow σ hp, cS, hp.two_le, Finset.sum_range_succ]

theorem hasProd_eq_zero {ι : Type*} {g : ι → ℂ} {x : ℂ} (h : HasProd g x) (i : ι)
    (hi : g i = 0) : x = 0 := by
  classical
  have h0 : Tendsto (fun s : Finset ι => ∏ b ∈ s, g b) atTop (𝓝 0) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop {i}] with s hs
    exact (prod_eq_zero (hs (mem_singleton_self i)) hi).symm
  exact tendsto_nhds_unique h h0

/-- **A097945, Re z > 1**: Sum_{n>=1} mu(n)/phi(n)^z = 0, absolutely. -/
theorem A097945_re_gt_one (z : ℂ) (hz : 1 < z.re) : HasSum (fz z) 0 := by
  have hsum : Summable (‖fz z ·‖) := by
    simpa [norm_fz] using summable_Fz hz
  have hP := EulerProduct.eulerProduct_hasProd (f := fz z) (fz_one z) (fz_mul z) hsum (fz_zero z)
  have h2 : ∑' e : ℕ, fz z ((⟨2, Nat.prime_two⟩ : Nat.Primes) ^ e) = 0 := by
    rw [tsum_eq_sum (s := range 2) (fun e he => by
      simp only [fz]
      rw [moebius_prime_pow_ge_two Nat.prime_two (by simp at he; omega)]
      simp)]
    simp [fz, Finset.sum_range_succ, moebius_apply_prime Nat.prime_two,
      Nat.totient_prime Nat.prime_two]
  have hx := hasProd_eq_zero hP _ h2
  rw [← hx]
  exact (hsum.of_norm).hasSum


/-! Part 2: s = 1, conditional on Landau's Sum mu(n)/n = 0. -/

/-- mu(n)/phi(n). -/
noncomputable def fA : ArithmeticFunction ℝ := ⟨fun n => (moebius n : ℝ) / (n.totient : ℝ), by simp⟩
/-- 1/n. -/
noncomputable def hA : ArithmeticFunction ℝ := ⟨fun n => 1 / (n : ℝ), by simp⟩
/-- mu(n)/n. -/
noncomputable def gA : ArithmeticFunction ℝ := ⟨fun n => (moebius n : ℝ) / (n : ℝ), by simp⟩
/-- k = (mu/phi) * (1/id). -/
noncomputable def kA : ArithmeticFunction ℝ := fA * hA

theorem fA_apply (n : ℕ) : fA n = (moebius n : ℝ) / (n.totient : ℝ) := rfl
theorem hA_apply (n : ℕ) : hA n = 1 / (n : ℝ) := rfl
theorem gA_apply (n : ℕ) : gA n = (moebius n : ℝ) / (n : ℝ) := rfl

theorem hA_mul_gA : hA * gA = 1 := by
  ext n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have key : (hA * gA) n =
      (1 / (n : ℝ)) * (((ζ : ArithmeticFunction ℝ) * (μ : ArithmeticFunction ℝ)) n) := by
    simp only [mul_apply, Finset.mul_sum]
    refine sum_congr rfl (fun x hx => ?_)
    have hx' := Nat.mem_divisorsAntidiagonal.mp hx
    have h1 : x.1 ≠ 0 := by
      intro h; rw [h, zero_mul] at hx'; exact hx'.2 hx'.1.symm
    have h2 : x.2 ≠ 0 := by
      intro h; rw [h, mul_zero] at hx'; exact hx'.2 hx'.1.symm
    rw [hA_apply, gA_apply, natCoe_apply, intCoe_apply, zeta_apply]
    simp only [h1, ↓reduceIte, Nat.cast_one]
    rw [← hx'.1]
    push_cast
    field_simp
  rw [key, coe_zeta_mul_coe_moebius]
  rcases eq_or_ne n 1 with rfl | h1
  · simp
  · simp [one_apply_ne h1]

theorem kA_mul_gA : kA * gA = fA := by
  rw [kA, mul_assoc, hA_mul_gA, mul_one]

theorem fA_mult : IsMultiplicative fA := by
  refine ⟨by simp [fA_apply], fun {m n} h => ?_⟩
  simp only [fA_apply, Nat.totient_mul h, isMultiplicative_moebius.map_mul_of_coprime h,
    Int.cast_mul, Nat.cast_mul]
  rw [mul_div_mul_comm]

theorem hA_mult : IsMultiplicative hA := by
  refine ⟨by simp [hA_apply], fun {m n} _ => ?_⟩
  simp only [hA_apply, Nat.cast_mul]
  rw [one_div_mul_one_div]

theorem kA_mult : IsMultiplicative kA := fA_mult.mul hA_mult

theorem kA_prime_pow_succ {p : ℕ} (hp : p.Prime) (e : ℕ) :
    kA (p ^ (e + 1)) = -(1 / ((p : ℝ) - 1)) * (1 / (p : ℝ)) ^ (e + 1) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hp0 : (p : ℝ) ≠ 0 := by positivity
  have hp2 : (p : ℝ) - 1 ≠ 0 := by linarith
  rw [kA, mul_apply, Nat.sum_divisorsAntidiagonal (fun a b => fA a * hA b),
    Nat.sum_divisors_prime_pow hp, sum_range_succ', sum_range_succ']
  have hz : ∀ i ∈ range e, fA (p ^ (i + 1 + 1)) * hA (p ^ (e + 1) / p ^ (i + 1 + 1)) = 0 := by
    intro i _
    rw [fA_apply, moebius_prime_pow_ge_two hp (by omega)]
    simp
  have hdiv : p ^ (e + 1) / p = p ^ e := by rw [pow_succ, Nat.mul_div_cancel _ hp.pos]
  rw [sum_eq_zero hz, fA_apply, fA_apply, hA_apply, hA_apply, pow_zero, Nat.div_one,
    zero_add, pow_one, moebius_apply_prime hp, Nat.totient_prime hp, hdiv]
  simp only [moebius_apply_one, Nat.totient_one]
  push_cast [Nat.cast_sub hp.one_le]
  simp only [one_div_pow, pow_succ]
  field_simp
  ring

theorem kA_abs_succ {p : ℕ} (hp : p.Prime) (e : ℕ) :
    |kA (p ^ (e + 1))| = (1 / ((p : ℝ) - 1)) * (1 / (p : ℝ)) ^ (e + 1) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have h1 : 0 < 1 / ((p : ℝ) - 1) := by
    have : 0 < (p : ℝ) - 1 := by linarith
    positivity
  have h2 : 0 < (1 / (p : ℝ)) ^ (e + 1) := by positivity
  rw [kA_prime_pow_succ hp, abs_mul, abs_neg, abs_of_pos h1, abs_of_pos h2]

theorem summable_abs_kA : Summable (fun n => |kA n|) := by
  refine summable_of_mult (fun n => |kA n|) (cS 2) (by simp) (by simp [kA_mult.map_one])
    ?_ (fun n => abs_nonneg _) ?_ (summable_cS (by norm_num)) cS_nonneg ?_
  · intro m n h
    simp only [kA_mult.map_mul_of_coprime h, abs_mul]
  · intro p hp
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    rw [← summable_nat_add_iff 1]
    have hg : Summable (fun e : ℕ => (1 / ((p : ℝ) - 1)) * (1 / (p : ℝ)) ^ (e + 1)) := by
      refine Summable.mul_left _ ?_
      refine (summable_geometric_of_lt_one (by positivity) ?_).comp_injective (add_left_injective 1)
      rw [div_lt_one (by linarith)]; exact hp1
    refine hg.congr (fun e => ?_)
    rw [kA_abs_succ hp]
  · intro p hp
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    have hq : (1 / (p : ℝ)) < 1 := by rw [div_lt_one (by linarith)]; exact hp1
    have hq0 : 0 ≤ (1 / (p : ℝ)) := by positivity
    have hs : Summable (fun e : ℕ => |kA (p ^ (e + 1))|) := by
      have hg : Summable (fun e : ℕ => (1 / ((p : ℝ) - 1)) * (1 / (p : ℝ)) ^ (e + 1)) :=
        ((summable_geometric_of_lt_one hq0 hq).comp_injective (add_left_injective 1)).mul_left _
      refine hg.congr (fun e => ?_)
      rw [kA_abs_succ hp]
    have hs0 : Summable (fun e : ℕ => |kA (p ^ e)|) := by
      rw [← summable_nat_add_iff 1]; exact hs
    rw [hs0.tsum_eq_zero_add]
    have h1 : ∑' e : ℕ, |kA (p ^ (e + 1))| = 1 / ((p : ℝ) - 1) ^ 2 := by
      have : ∀ e : ℕ, |kA (p ^ (e + 1))| = (1 / ((p : ℝ) - 1) * (1 / p)) * (1 / (p : ℝ)) ^ e := by
        intro e
        rw [kA_abs_succ hp, pow_succ]
        ring
      simp only [this]
      rw [tsum_mul_left, tsum_geometric_of_lt_one hq0 hq]
      have : (p : ℝ) - 1 ≠ 0 := by linarith
      field_simp
    rw [h1]
    simp [cS, hp.two_le, kA_mult.map_one]

/-- **A097945, s = 1 (conditional)**: if Sum_{m<=N} mu(m)/m -> 0, then
Sum_{n<=N} mu(n)/phi(n) -> 0. -/
theorem sum_mu_div_phi_tendsto
    (hL : Tendsto (fun N : ℕ => ∑ m ∈ Ioc 0 N, (moebius m : ℝ) / m) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => ∑ n ∈ Ioc 0 N, (moebius n : ℝ) / n.totient) atTop (𝓝 0) := by
  set A : ℕ → ℝ := fun M => ∑ m ∈ Ioc 0 M, gA m with hAdef
  have hA0 : Tendsto A atTop (𝓝 0) := by simpa [A, gA_apply] using hL
  obtain ⟨B, hB⟩ := isBounded_iff_forall_norm_le.mp (Metric.isBounded_range_of_tendsto A hA0)
  have hB' : ∀ M, |A M| ≤ B := fun M => by
    simpa [Real.norm_eq_abs] using hB (A M) ⟨M, rfl⟩
  have hB0 : 0 ≤ B := le_trans (abs_nonneg _) (hB' 0)
  let T : ℕ → ℕ → ℝ := fun N => Set.indicator (↑(Ioc 0 N)) (fun n => kA n * A (N / n))
  have hsumT : ∀ N, ∑ n ∈ Ioc 0 N, (moebius n : ℝ) / n.totient = ∑' n, T N n := by
    intro N
    have e1 : ∑ n ∈ Ioc 0 N, (moebius n : ℝ) / n.totient = ∑ n ∈ Ioc 0 N, (kA * gA) n := by
      rw [kA_mul_gA]; rfl
    rw [e1, sum_Ioc_mul_eq_sum_sum, tsum_eq_sum (s := Ioc 0 N)
      (fun n hn => Set.indicator_of_notMem (by rw [Finset.mem_coe]; exact hn) _)]
    refine sum_congr rfl (fun n hn => ?_)
    have hmem : n ∈ (↑(Ioc 0 N) : Set ℕ) := by rw [Finset.mem_coe]; exact hn
    exact (Set.indicator_of_mem hmem (fun n => kA n * A (N / n))).symm
  simp_rw [hsumT]
  have hlim := tendsto_tsum_of_dominated_convergence (𝓕 := atTop) (f := T) (g := fun _ => (0 : ℝ))
    (bound := fun n => |kA n| * B) (summable_abs_kA.mul_right B) ?_ ?_
  · simpa using hlim
  · intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [T]
    · have h1 : Tendsto (fun N : ℕ => A (N / n)) atTop (𝓝 0) :=
        hA0.comp (Nat.tendsto_div_const_atTop hn.ne')
      have h2 : Tendsto (fun N : ℕ => kA n * A (N / n)) atTop (𝓝 0) := by
        simpa using h1.const_mul (kA n)
      refine h2.congr' ?_
      filter_upwards [eventually_ge_atTop n] with N hN
      have hmem : n ∈ (↑(Ioc 0 N) : Set ℕ) := by rw [Finset.mem_coe, Finset.mem_Ioc]; omega
      exact (Set.indicator_of_mem hmem (fun n => kA n * A (N / n))).symm
  · refine Eventually.of_forall (fun N n => ?_)
    simp only [T, Set.indicator_apply]
    split_ifs
    · rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_left (hB' _) (abs_nonneg _)
    · simpa using mul_nonneg (abs_nonneg (kA n)) hB0

/-- **A097945 (conditional on Sum mu(n)/n = 0)**: the partial sums of
Sum mu(n)/phi(n) and of Sum a(n)/phi(n)^2 tend to 0. -/
theorem A097945_conditional
    (hL : Tendsto (fun N : ℕ => ∑ m ∈ Ioc 0 N, (moebius m : ℝ) / m) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => ∑ n ∈ Ioc 0 N, (moebius n : ℝ) / n.totient) atTop (𝓝 0) ∧
    Tendsto (fun N : ℕ => ∑ n ∈ Ioc 0 N, (a n : ℝ) / (n.totient : ℝ) ^ 2) atTop (𝓝 0) := by
  have h := sum_mu_div_phi_tendsto hL
  refine ⟨h, h.congr (fun N => sum_congr rfl (fun n hn => ?_))⟩
  have hn : 0 < n := (mem_Ioc.mp hn).1
  have ht : (n.totient : ℝ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr hn).ne'
  unfold a
  push_cast
  field_simp

/-- Landau's form of the prime number theorem, Sum_{m<=N} mu(m)/m -> 0,
from `mu_pnt_alt` (vendored PrimeNumberTheoremAnd). -/
theorem sum_mu_div_tendsto :
    Tendsto (fun N : ℕ => ∑ m ∈ Ioc 0 N, (moebius m : ℝ) / m) atTop (𝓝 0) := by
  have h := (Asymptotics.isLittleO_one_iff ℝ).mp mu_pnt_alt
  have hN : Tendsto (fun N : ℕ => (N : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  have hsum : ∀ N : ℕ, ∑ n ∈ range (N + 1), (moebius n : ℝ) / n =
      ∑ m ∈ Ioc 0 N, (moebius m : ℝ) / m := by
    intro N
    induction N with
    | zero => simp
    | succ n ih => rw [Finset.sum_range_succ, ih, Finset.sum_Ioc_succ_top (Nat.zero_le n)]
  refine (h.comp hN).congr (fun N => ?_)
  have hfl : ⌊(N : ℝ) + 1⌋₊ = N + 1 := by exact_mod_cast Nat.floor_natCast (N + 1)
  simp only [Function.comp_apply, hfl]
  exact hsum N

/-- **A097945, s = 1**: the partial sums of Sum mu(n)/phi(n) and of
Sum a(n)/phi(n)^2 tend to 0. -/
theorem A097945_s_one :
    Tendsto (fun N : ℕ => ∑ n ∈ Ioc 0 N, (moebius n : ℝ) / n.totient) atTop (𝓝 0) ∧
    Tendsto (fun N : ℕ => ∑ n ∈ Ioc 0 N, (a n : ℝ) / (n.totient : ℝ) ^ 2) atTop (𝓝 0) :=
  A097945_conditional sum_mu_div_tendsto

