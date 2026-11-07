import Mathlib
import OpenProblemsLib.Dwork

/-!
# p-local Dwork lemma for exp-log series with rational coefficients

Everything is stated with the `p`-adic norm on `ℚ`.

* `PV p k x`: `padicNorm p x ≤ p^(-k)`, i.e. `p^k ∣ x` in `ℤ_(p)` (`k : ℤ` may be negative).
  Closure lemmas `PV_add`, `PV_sub`, `PV_neg`, `PV_sum`, `PV_mul`, `PV_mono`, `PV_div_nat`
  (dividing by `n` costs `v_p n`), `PV_int`, `PV_dvd` (`p^a ∣ z` in `ℤ`), `PV_ppow`,
  `PV_inv_ppow`, `PV_inv_coprime`.
* `int_of_PV`: a rational with `PV p 0` at every prime is an integer.
* `approx`: a `p`-integral rational is congruent to an integer modulo any `p^K`.
* `expQ b`: the coefficients of `exp (∑_{n ≥ 1} b n x^n / n)` for `b : ℕ → ℚ`, by the same
  recurrence as `OpenProblemsLib.Dwork.expCoeff`; `expQ_cast`: the two agree on integer `b`.
* `expQ_perturb`: if `b ≡ b' (mod p^K)` on `1..N`, `b'` is `p`-integral there and `expQ b'` is
  `p`-integral up to `N`, then `expQ b n ≡ expQ b' n (mod p^(K - v_p(n!)))` for `n ≤ N`.
* `LGq p b`: the Gauss congruences at the single prime `p` for `b : ℕ → ℚ`.
* `cQ_pint`: `p`-integral `b` with `LGq p b` has `p`-integral Dwork exponents
  `cQ b n = (b n - ∑_{d ∣ n, d < n} d cQ b d) / n`.
* `expQ_pint_of_LGq` (p-local Dwork lemma): `p`-integral `b` with Gauss congruences at `p` gives
  `p`-integral `expQ b n` for every `n`. Proof: approximate each `cQ b d` by an integer `c' d`
  modulo `p^K` with `K = v_p(n!)`, apply the integral lemma `expCoeff_int_of_euler` to
  `b' n = ∑_{d ∣ n} d c' d`, and conclude with `expQ_perturb`.
-/

namespace OpenProblemsLib.DworkLocal

open OpenProblemsLib.Dwork

/-- `p^k ∣ x` in `ℤ_(p)`. -/
def PV (p : ℕ) (k : ℤ) (x : ℚ) : Prop := padicNorm p x ≤ (p : ℚ) ^ (-k)

section
variable {p : ℕ} [hp : Fact p.Prime]

theorem p_pos : (0 : ℚ) < p := by exact_mod_cast hp.out.pos

theorem PV_zero (k : ℤ) : PV p k 0 := by
  unfold PV; rw [padicNorm.zero]; exact (zpow_pos p_pos _).le

theorem PV_mono {k l : ℤ} {x : ℚ} (h : PV p k x) (hlk : l ≤ k) : PV p l x := by
  unfold PV at *
  refine h.trans (zpow_le_zpow_right₀ ?_ (by omega))
  exact_mod_cast hp.out.one_lt.le

theorem PV_add {k : ℤ} {x y : ℚ} (hx : PV p k x) (hy : PV p k y) : PV p k (x + y) :=
  padicNorm.nonarchimedean.trans (max_le hx hy)

omit hp in
theorem PV_neg {k : ℤ} {x : ℚ} (hx : PV p k x) : PV p k (-x) := by
  unfold PV at *; rwa [padicNorm.neg]

theorem PV_sub {k : ℤ} {x y : ℚ} (hx : PV p k x) (hy : PV p k y) : PV p k (x - y) :=
  padicNorm.sub.trans (max_le hx hy)

theorem PV_sum {ι : Type*} (s : Finset ι) (f : ι → ℚ) {k : ℤ} (h : ∀ i ∈ s, PV p k (f i)) :
    PV p k (∑ i ∈ s, f i) :=
  padicNorm.sum_le' h (zpow_pos p_pos _).le

theorem PV_mul {k l : ℤ} {x y : ℚ} (hx : PV p k x) (hy : PV p l y) : PV p (k + l) (x * y) := by
  unfold PV at *
  rw [padicNorm.mul, neg_add, zpow_add₀ p_pos.ne']
  exact mul_le_mul hx hy (padicNorm.nonneg _) (zpow_pos p_pos _).le

theorem PV_int (z : ℤ) : PV p 0 (z : ℚ) := by
  unfold PV; simpa using padicNorm.of_int (p := p) z

theorem PV_dvd (a : ℕ) (z : ℤ) (h : ((p : ℤ) ^ a) ∣ z) : PV p a (z : ℚ) := by
  unfold PV
  have := (padicNorm.dvd_iff_norm_le (p := p) (n := a) (z := z)).mp (by exact_mod_cast h)
  simpa using this

theorem PV_div_nat {k : ℤ} {x : ℚ} (hx : PV p k x) (n : ℕ) (hn : n ≠ 0) :
    PV p (k - padicValNat p n) (x / n) := by
  unfold PV at *
  rw [padicNorm.div, padicNorm.eq_zpow_of_nonzero (by exact_mod_cast hn : (n : ℚ) ≠ 0),
    ← padicValRat_of_nat, div_eq_mul_inv, ← zpow_neg, neg_neg,
    show -(k - (padicValNat p n : ℤ)) = -k + padicValNat p n by ring, zpow_add₀ p_pos.ne']
  exact mul_le_mul_of_nonneg_right hx (zpow_pos p_pos _).le

theorem norm_ppow (e : ℕ) : padicNorm p ((p : ℚ) ^ e) = (p : ℚ) ^ (-(e : ℤ)) := by
  induction e with
  | zero => simp
  | succ e ih =>
    rw [pow_succ, padicNorm.mul, ih, padicNorm.padicNorm_p_of_prime]
    push_cast
    rw [neg_add, zpow_add₀ p_pos.ne', zpow_neg_one]

theorem PV_ppow (e : ℕ) : PV p e ((p : ℚ) ^ e) := by
  unfold PV; rw [norm_ppow]

theorem PV_inv_ppow (e : ℕ) : PV p (-(e : ℤ)) (1 / (p : ℚ) ^ e) := by
  unfold PV; rw [padicNorm.div, padicNorm.one, norm_ppow, one_div, ← zpow_neg]

/-- `1 / m^e` is a `p`-adic unit when `p ∤ m`. -/
theorem PV_inv_coprime (m e : ℕ) (hm : ¬ p ∣ m) : PV p 0 (1 / (m : ℚ) ^ e) := by
  have hnd : ¬ p ∣ m ^ e := fun h => hm (hp.out.dvd_of_dvd_pow h)
  have h1 := (padicNorm.nat_eq_one_iff (p := p) (m ^ e)).mpr hnd
  push_cast at h1
  unfold PV; rw [padicNorm.div, padicNorm.one, h1]; simp

theorem not_dvd_den {x : ℚ} (h : PV p 0 x) : ¬ p ∣ x.den := by
  intro hd
  have hnum : ¬ (p : ℤ) ∣ x.num := by
    intro hn
    have h1 : p ∣ x.num.natAbs := Int.natCast_dvd.mp hn
    have h2 := Nat.dvd_gcd h1 hd
    rw [x.reduced.gcd_eq_one] at h2
    exact hp.out.one_lt.ne' (Nat.dvd_one.mp h2)
  have h' : padicNorm p ((x.num : ℚ) / (x.den : ℚ)) ≤ 1 := by
    rw [Rat.num_div_den]; simpa [PV] using h
  rw [padicNorm.div, (padicNorm.int_eq_one_iff _).mpr hnum] at h'
  have h2 := (padicNorm.nat_lt_one_iff (p := p) x.den).mpr hd
  have h3 : 0 < padicNorm p (x.den : ℚ) :=
    lt_of_le_of_ne (padicNorm.nonneg _) (Ne.symm (padicNorm.nonzero (by positivity)))
  rw [div_le_one h3] at h'
  linarith

/-- A `p`-integral rational is congruent to an integer modulo `p^K`. -/
theorem approx {x : ℚ} (h : PV p 0 x) (K : ℕ) : ∃ z : ℤ, PV p K (x - z) := by
  have hd := not_dvd_den h
  have hc : IsCoprime ((p : ℤ) ^ K) (x.den : ℤ) :=
    IsCoprime.pow_left (Nat.isCoprime_iff_coprime.mpr ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hd))
  obtain ⟨u, v, huv⟩ := hc
  refine ⟨x.num * v, ?_⟩
  have hden : (x.den : ℚ) ≠ 0 := by positivity
  have hq : (u : ℚ) * (p : ℚ) ^ K + v * x.den = 1 := by exact_mod_cast huv
  have hx : x * x.den = x.num := Rat.mul_den_eq_num x
  have e : x - ((x.num * v : ℤ) : ℚ) = ((x.num * u : ℤ) : ℚ) * (p : ℚ) ^ K / (x.den : ℕ) := by
    rw [eq_div_iff hden]; push_cast
    linear_combination hx - (x.num : ℚ) * hq
  rw [e]
  have := PV_div_nat (PV_mul (PV_int (p := p) (x.num * u)) (PV_ppow K)) x.den x.den_nz
  rw [padicValNat.eq_zero_of_not_dvd hd] at this
  simpa using this

end

/-- A rational that is `p`-integral at every prime is an integer. -/
theorem int_of_PV {x : ℚ} (h : ∀ p : ℕ, p.Prime → PV p 0 x) : ∃ z : ℤ, x = z := by
  refine ⟨x.num, ?_⟩
  have hden : x.den = 1 := by
    by_contra hne
    have hpp := Nat.minFac_prime hne
    have := Fact.mk hpp
    exact not_dvd_den (h _ hpp) (Nat.minFac_dvd _)
  exact (Rat.coe_int_num_of_den_eq_one hden).symm

/-! ## exp-log series over `ℚ` -/

/-- Coefficients of `exp (∑_{n ≥ 1} b n x^n / n)` for rational `b`. -/
def expQ (b : ℕ → ℚ) : ℕ → ℚ
  | 0 => 1
  | n + 1 => (∑ j : Fin (n + 1), b (j + 1) * expQ b (n - j)) / (n + 1)
decreasing_by omega

theorem expQ_zero (b : ℕ → ℚ) : expQ b 0 = 1 := by rw [expQ]

theorem expQ_succ (b : ℕ → ℚ) (n : ℕ) :
    ((n : ℚ) + 1) * expQ b (n + 1) = ∑ j ∈ Finset.range (n + 1), b (j + 1) * expQ b (n - j) := by
  rw [expQ, Fin.sum_univ_eq_sum_range (fun j => b (j + 1) * expQ b (n - j)) (n + 1)]
  have : ((n : ℚ) + 1) ≠ 0 := by positivity
  field_simp

theorem expQ_cast (b : ℕ → ℤ) (n : ℕ) : expQ (fun m => (b m : ℚ)) n = expCoeff b n :=
  eq_expCoeff_of_rec b _ n (expQ_zero _) (fun k _ => expQ_succ _ k) n le_rfl

section
variable {p : ℕ} [hp : Fact p.Prime]

theorem vfact_mono {k N : ℕ} (h : k ≤ N) : padicValNat p k.factorial ≤ padicValNat p N.factorial :=
  (padicValNat_dvd_iff_le (Nat.factorial_ne_zero N)).mp
    (pow_padicValNat_dvd.trans (Nat.factorial_dvd_factorial h))

theorem vfact_succ (n : ℕ) :
    padicValNat p (n + 1).factorial = padicValNat p (n + 1) + padicValNat p n.factorial := by
  rw [Nat.factorial_succ, padicValNat.mul (by omega) (Nat.factorial_ne_zero n)]

/-- Perturbation: `b ≡ b' (mod p^K)` gives `expQ b ≡ expQ b' (mod p^(K - v_p(n!)))`. -/
theorem expQ_perturb (b b' : ℕ → ℚ) (K N : ℕ) (hK : padicValNat p N.factorial ≤ K)
    (hb' : ∀ m, 1 ≤ m → m ≤ N → PV p 0 (b' m))
    (hA' : ∀ n, n ≤ N → PV p 0 (expQ b' n))
    (hd : ∀ m, 1 ≤ m → m ≤ N → PV p K (b m - b' m)) :
    ∀ n, n ≤ N → PV p ((K : ℤ) - padicValNat p n.factorial) (expQ b n - expQ b' n) ∧
      PV p 0 (expQ b n) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    have hfirst : PV p ((K : ℤ) - padicValNat p n.factorial) (expQ b n - expQ b' n) := by
      rcases n with _ | n
      · rw [expQ_zero, expQ_zero, sub_self]; exact PV_zero _
      · set S := ∑ j ∈ Finset.range (n + 1),
          ((b (j + 1) - b' (j + 1)) * expQ b (n - j) + b' (j + 1) * (expQ b (n - j) - expQ b' (n - j)))
        have key : ((n : ℚ) + 1) * (expQ b (n + 1) - expQ b' (n + 1)) = S := by
          rw [mul_sub, expQ_succ, expQ_succ, ← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl; intro j _; ring
        have hS : PV p ((K : ℤ) - padicValNat p n.factorial) S := by
          apply PV_sum; intro j hj
          rw [Finset.mem_range] at hj
          have ihj := ih (n - j) (by omega) (by omega)
          have hv := vfact_mono (p := p) (show n - j ≤ n by omega)
          apply PV_add
          · exact PV_mono (PV_mul (hd (j + 1) (by omega) (by omega)) ihj.2) (by omega)
          · exact PV_mono (PV_mul (hb' (j + 1) (by omega) (by omega)) ihj.1) (by omega)
        have hδ : expQ b (n + 1) - expQ b' (n + 1) = S / ((n + 1 : ℕ) : ℚ) := by
          rw [eq_div_iff (by positivity)]; push_cast; rw [mul_comm]; exact key
        rw [hδ]
        have := PV_div_nat hS (n + 1) (by omega)
        rw [vfact_succ]; push_cast at this ⊢
        convert this using 1; ring
    refine ⟨hfirst, ?_⟩
    have hv := vfact_mono (p := p) hn
    have e : expQ b n = expQ b' n + (expQ b n - expQ b' n) := by ring
    rw [e]; exact PV_add (hA' n hn) (PV_mono hfirst (by omega))

/-! ## p-local Dwork lemma -/

/-- The Gauss congruences at the single prime `p`, for rational sequences. -/
def LGq (p : ℕ) (b : ℕ → ℚ) : Prop :=
  ∀ a m : ℕ, 1 ≤ a → PV p a (b (m * p ^ a) - b (m * p ^ (a - 1)))

end

/-- Dwork exponents over `ℚ`: `b n = ∑_{d ∣ n} d cQ b d`. -/
def cQ (b : ℕ → ℚ) (n : ℕ) : ℚ :=
  if n = 0 then 0 else (b n - ∑ d ∈ n.properDivisors.attach, (d.1 : ℚ) * cQ b d.1) / n
termination_by n
decreasing_by exact (Nat.mem_properDivisors.mp d.2).2

theorem cQ_eq (b : ℕ → ℚ) (n : ℕ) (hn : n ≠ 0) :
    cQ b n = (b n - ∑ d ∈ n.properDivisors, (d : ℚ) * cQ b d) / n := by
  rw [cQ]
  simp only [hn, ↓reduceIte]
  congr 2
  exact Finset.sum_attach n.properDivisors (fun d => (d : ℚ) * cQ b d)

theorem cQ_zero (b : ℕ → ℚ) : cQ b 0 = 0 := by rw [cQ]; simp

theorem cQ_sum (b : ℕ → ℚ) (n : ℕ) (hn : 1 ≤ n) : b n = ∑ d ∈ n.divisors, (d : ℚ) * cQ b d := by
  rw [← Nat.insert_self_properDivisors (by omega : n ≠ 0),
    Finset.sum_insert Nat.self_notMem_properDivisors, cQ_eq b n (by omega)]
  have h : (n : ℚ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have : (n : ℚ) * ((b n - ∑ d ∈ n.properDivisors, (d : ℚ) * cQ b d) / n) =
      b n - ∑ d ∈ n.properDivisors, (d : ℚ) * cQ b d := by field_simp
  rw [this]; ring

section
variable {p : ℕ} [hp : Fact p.Prime]

theorem cQ_pint (b : ℕ → ℚ) (hb : ∀ m, 1 ≤ m → PV p 0 (b m)) (hG : LGq p b) :
    ∀ n, PV p 0 (cQ b n) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [cQ_zero]; exact PV_zero _
    set S := ∑ d ∈ n.properDivisors, (d : ℚ) * cQ b d with hS
    set v := n.factorization p with hv
    have hX : PV p v (b n - S) := by
      by_cases hv0 : v = 0
      · rw [hv0]; push_cast
        apply PV_sub (hb n hn)
        apply PV_sum; intro d hd
        have hdl := (Nat.mem_properDivisors.mp hd).2
        simpa using PV_mul (PV_int (p := p) (d : ℤ)) (ih d hdl)
      set m := n / p ^ v with hm
      have hnm : n = m * p ^ v := by
        rw [hm, hv, mul_comm]; exact (Nat.ordProj_mul_ordCompl_eq_self n p).symm
      have hpm : ¬ p ∣ m := Nat.not_dvd_ordCompl hp.out (by omega)
      set n' := m * p ^ (v - 1) with hn'
      have hn'n : n' ∣ n := by
        rw [hnm]; exact mul_dvd_mul_left m (Nat.pow_dvd_pow p (by omega))
      have hm0 : 1 ≤ m := by
        rcases Nat.eq_zero_or_pos m with h | h
        · rw [h] at hnm; omega
        · exact h
      have hn'lt : n' < n := by
        rw [hnm, hn']
        have : p ^ (v - 1) < p ^ v := Nat.pow_lt_pow_right hp.out.one_lt (by omega)
        exact Nat.mul_lt_mul_of_pos_left this (by omega)
      have hn'1 : 1 ≤ n' := by
        have : 1 ≤ p ^ (v - 1) := Nat.one_le_pow _ _ hp.out.pos
        rw [hn']; nlinarith
      have hsub : n'.divisors ⊆ n.properDivisors := by
        intro d hd
        rw [Nat.mem_divisors] at hd
        rw [Nat.mem_properDivisors]
        exact ⟨hd.1.trans hn'n, lt_of_le_of_lt (Nat.le_of_dvd (by omega) hd.1) hn'lt⟩
      have hsplit := Finset.sum_sdiff hsub (f := fun d : ℕ => (d : ℚ) * cQ b d)
      have hXe : b n - S = (b (m * p ^ v) - b (m * p ^ (v - 1))) -
          ∑ d ∈ (n.properDivisors \ n'.divisors : Finset ℕ), (d : ℚ) * cQ b d := by
        rw [hS, ← hsplit, ← cQ_sum b n' hn'1, ← hnm, hn']; ring
      rw [hXe]
      apply PV_sub (hG v m (by omega))
      apply PV_sum
      intro d hd
      rw [Finset.mem_sdiff, Nat.mem_properDivisors, Nat.mem_divisors] at hd
      have hpd := pow_dvd_of_not_dvd p v m d hp.out (by omega) hpm (by rw [← hnm]; exact hd.1.1)
        (fun h => hd.2 ⟨h, by rw [hn']; exact Nat.ne_of_gt (Nat.mul_pos hm0 (pow_pos hp.out.pos _))⟩)
      have h1 : PV p v ((d : ℤ) : ℚ) := PV_dvd v d (by exact_mod_cast hpd)
      simpa using PV_mul h1 (ih d hd.1.2)
    rw [cQ_eq b n (by omega)]
    have := PV_div_nat hX n (by omega)
    rw [← Nat.factorization_def n hp.out, ← hv, sub_self] at this
    exact this

/-- p-local Dwork lemma: Gauss congruences at `p` for a `p`-integral `b` make every coefficient of
`exp (∑ b n x^n / n)` `p`-integral. -/
theorem expQ_pint_of_LGq (b : ℕ → ℚ) (hb : ∀ m, 1 ≤ m → PV p 0 (b m)) (hG : LGq p b) (n : ℕ) :
    PV p 0 (expQ b n) := by
  have hc := cQ_pint b hb hG
  set K := padicValNat p n.factorial
  choose c' hc' using fun d => approx (hc d) K
  set b' : ℕ → ℤ := fun k => ∑ d ∈ k.divisors, (d : ℤ) * c' d
  have hint := expCoeff_int_of_euler b' c' (fun k _ => rfl)
  have hA' : ∀ k, k ≤ n → PV p 0 (expQ (fun m => (b' m : ℚ)) k) := by
    intro k _
    obtain ⟨z, hz⟩ := hint k
    rw [expQ_cast, hz]; exact PV_int z
  have hd : ∀ m, 1 ≤ m → m ≤ n → PV p K (b m - (b' m : ℚ)) := by
    intro m hm _
    rw [cQ_sum b m hm]
    simp only [b']; push_cast
    rw [← Finset.sum_sub_distrib]
    apply PV_sum; intro d _
    have := PV_mul (PV_int (p := p) (d : ℤ)) (hc' d)
    rw [zero_add] at this
    convert this using 1; push_cast; ring
  exact (expQ_perturb b _ K n le_rfl (fun m _ _ => PV_int _) hA' hd n le_rfl).2

end

end OpenProblemsLib.DworkLocal
