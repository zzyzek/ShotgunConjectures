import Mathlib

/-!
# Dwork's lemma and Euler products for exp-log integer series

All series are handled through coefficient recurrences, not through Mathlib's `exp`/`log` of
power series.

* `expCoeff b n`: the coefficients of `exp (∑_{n ≥ 1} b n x^n / n)` over `ℚ`, i.e. the unique `A`
  with `A 0 = 1` and `(n+1) A (n+1) = ∑_{j=0}^{n} b (j+1) A (n-j)`.
* `expCoeff_int_of_euler`: if `b n = ∑_{d ∣ n} d * c d` with `c : ℕ → ℤ` then every
  `expCoeff b n` is an integer (the truncated Euler product `∏_d (1 - x^d)^(-c d)` in `ℤ⟦X⟧`
  has the same coefficients).
* `LGp p b`: the Gauss congruences at the prime `p`,
  `p^a ∣ b (m p^a) - b (m p^(a-1))` for all `a ≥ 1`, `m`.
* `dwork`: Gauss congruences at every prime give `b n = ∑_{d ∣ n} d * cOf b d` with integer
  `cOf b` (Dwork's lemma, integral form).
* `expCoeff_int_of_gauss`: the two combined. `LGp_of_euler`: the converse of `dwork`.
* `euler_of_expCoeff_int`, `gauss_of_expCoeff_int`: conversely, if every `expCoeff b n` is an
  integer then `b` has the Euler form and the Gauss congruences.
* Closure of `LGp p`: `LGp_add`, `LGp_neg`, `LGp_sub`, `LGp_const`, `LGp_mul`, `LGp_pow`,
  `LGp_sum`, `LGp_comp_mul` (subsequence `j ↦ b (j k)`), `LGp_pow_self` (`j ↦ u j ^ (j c)`),
  `LGp_zpow` (`j ↦ x ^ j`, from `pow_gauss`, Fermat-Euler).
* `expCoeff_congr`, `eq_expCoeff_of_rec`: `expCoeff b n` depends only on `b 1, ..., b n`, and
  any sequence satisfying the recurrence up to `N` equals it up to `N`.

Origin: OEIS/A181316/A181316_mathlib.lean (namespace `A181316`), itself copied from
OEIS/A207969.
-/

namespace OpenProblemsLib.Dwork

open PowerSeries

/-- θ = x d/dx -/
noncomputable def theta (f : ℤ⟦X⟧) : ℤ⟦X⟧ := PowerSeries.mk fun n => (n : ℤ) * coeff n f

theorem coeff_theta (f : ℤ⟦X⟧) (n : ℕ) : coeff n (theta f) = n * coeff n f := by
  simp [theta]

theorem theta_mul (f g : ℤ⟦X⟧) : theta (f * g) = theta f * g + f * theta g := by
  ext n
  rw [coeff_theta, map_add, coeff_mul, coeff_mul, coeff_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x hx
  have hx' := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
  rw [coeff_theta, coeff_theta, ← hx']
  push_cast; ring

/-- log-derivative relation θ f = B f -/
def LD (f B : ℤ⟦X⟧) : Prop := theta f = B * f

theorem LD_mul {f g B C : ℤ⟦X⟧} (h1 : LD f B) (h2 : LD g C) : LD (f * g) (B + C) := by
  unfold LD at *; rw [theta_mul, h1, h2]; ring

theorem theta_one : theta 1 = 0 := by
  ext n; rw [coeff_theta, coeff_one]; split_ifs with h <;> simp [h]

theorem LD_one : LD 1 0 := by unfold LD; rw [theta_one]; ring

theorem LD_pow {f B : ℤ⟦X⟧} (h : LD f B) (n : ℕ) : LD (f ^ n) ((n : ℤ⟦X⟧) * B) := by
  induction n with
  | zero => simpa using LD_one
  | succ n ih =>
    rw [pow_succ]
    have := LD_mul ih h
    convert this using 1; push_cast; ring

theorem LD_inv {f g B : ℤ⟦X⟧} (h : LD f B) (hfg : f * g = 1) : LD g (-B) := by
  unfold LD at *
  have h0 := congrArg theta hfg
  rw [theta_mul, theta_one, h] at h0
  calc theta g = (f * g) * theta g := by rw [hfg, one_mul]
    _ = g * (B * f * g + f * theta g) - g * B * (f * g) := by ring
    _ = -B * g := by rw [h0, hfg]; ring

/-- W d = Σ_j X^(d j) -/
noncomputable def Wd (d : ℕ) : ℤ⟦X⟧ := PowerSeries.mk fun n => if d ∣ n then 1 else 0

theorem Wd_mul (d : ℕ) (hd : 1 ≤ d) : (1 - X ^ d) * Wd d = 1 := by
  ext n
  rw [sub_mul, one_mul, map_sub, coeff_X_pow_mul', coeff_one]
  simp only [Wd, coeff_mk]
  have hiff : d ∣ n ↔ (d ≤ n ∧ d ∣ n - d) ∨ n = 0 := by
    constructor
    · intro h
      by_cases hn : n = 0
      · exact Or.inr hn
      · exact Or.inl ⟨Nat.le_of_dvd (by omega) h, Nat.dvd_sub h (dvd_refl d)⟩
    · rintro (⟨h1, h2⟩ | h)
      · have := Nat.dvd_add h2 (dvd_refl d); rwa [Nat.sub_add_cancel h1] at this
      · rw [h]; exact dvd_zero d
  by_cases hn : n = 0
  · subst hn; simp; omega
  · by_cases h : d ∣ n
    · have h' := (hiff.mp h).resolve_right hn
      simp [h, h'.1, h'.2, hn]
    · have h' : ¬ (d ≤ n ∧ d ∣ n - d) := fun h' => h (hiff.mpr (Or.inl h'))
      by_cases h1 : d ≤ n
      · have h2 : ¬ d ∣ n - d := fun h2 => h' ⟨h1, h2⟩
        simp [h, h1, h2, hn]
      · simp [h, h1, hn]

noncomputable def Gd (d : ℕ) : ℤ⟦X⟧ := (d : ℤ⟦X⟧) * X ^ d * Wd d

theorem theta_one_sub (d : ℕ) (hd1 : 1 ≤ d) : theta (1 - X ^ d) = -((d : ℤ⟦X⟧) * X ^ d) := by
  ext n
  rw [coeff_theta, map_sub, coeff_one, coeff_X_pow, map_neg, ← map_natCast (C (R := ℤ)) d,
    coeff_C_mul, coeff_X_pow]
  by_cases h0 : n = 0
  · subst h0; simp; omega
  · by_cases hd : n = d
    · subst hd; simp [h0]
    · simp [h0, hd]

theorem LD_one_sub (d : ℕ) (hd : 1 ≤ d) : LD (1 - X ^ d) (-Gd d) := by
  unfold LD Gd
  rw [theta_one_sub d hd]
  have := Wd_mul d hd
  calc -((d : ℤ⟦X⟧) * X ^ d) = -((d : ℤ⟦X⟧) * X ^ d) * ((1 - X ^ d) * Wd d) := by rw [this, mul_one]
    _ = _ := by ring

theorem LD_Wd (d : ℕ) (hd : 1 ≤ d) : LD (Wd d) (Gd d) := by
  have := LD_inv (LD_one_sub d hd) (Wd_mul d hd)
  rwa [neg_neg] at this

noncomputable def Fdc (d : ℕ) (c : ℤ) : ℤ⟦X⟧ :=
  if 0 ≤ c then Wd d ^ c.toNat else (1 - X ^ d) ^ (-c).toNat

theorem LD_Fdc (d : ℕ) (hd : 1 ≤ d) (c : ℤ) : LD (Fdc d c) ((c : ℤ⟦X⟧) * Gd d) := by
  unfold Fdc
  split_ifs with hc
  · have := LD_pow (LD_Wd d hd) c.toNat
    convert this using 2
    rw [show (c.toNat : ℤ⟦X⟧) = ((c.toNat : ℤ) : ℤ⟦X⟧) by push_cast; rfl, Int.toNat_of_nonneg hc]
  · have := LD_pow (LD_one_sub d hd) (-c).toNat
    convert this using 1
    rw [show ((-c).toNat : ℤ⟦X⟧) = (((-c).toNat : ℤ) : ℤ⟦X⟧) by push_cast; rfl,
      Int.toNat_of_nonneg (by omega)]
    push_cast; ring

theorem const_Wd (d : ℕ) : constantCoeff (Wd d) = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply]; simp [Wd]

theorem const_Fdc (d : ℕ) (hd : 1 ≤ d) (c : ℤ) : constantCoeff (Fdc d c) = 1 := by
  unfold Fdc
  split_ifs
  · rw [map_pow, const_Wd, one_pow]
  · rw [map_pow, map_sub, map_one, map_pow, constantCoeff_X, zero_pow (by omega), sub_zero,
      one_pow]

/-- truncated Euler product ∏_{d ≤ D} (1 - x^d)^(-c d) -/
noncomputable def EP (c : ℕ → ℤ) (D : ℕ) : ℤ⟦X⟧ := ∏ i ∈ Finset.range D, Fdc (i + 1) (c (i + 1))

noncomputable def EB (c : ℕ → ℤ) (D : ℕ) : ℤ⟦X⟧ :=
  ∑ i ∈ Finset.range D, (c (i + 1) : ℤ⟦X⟧) * Gd (i + 1)

theorem LD_EP (c : ℕ → ℤ) (D : ℕ) : LD (EP c D) (EB c D) := by
  induction D with
  | zero => simpa [EP, EB] using LD_one
  | succ D ih =>
    unfold EP EB
    rw [Finset.prod_range_succ, Finset.sum_range_succ]
    exact LD_mul ih (LD_Fdc (D + 1) (by omega) _)

theorem const_EP (c : ℕ → ℤ) (D : ℕ) : constantCoeff (EP c D) = 1 := by
  unfold EP
  rw [map_prod]
  exact Finset.prod_eq_one (fun i _ => const_Fdc (i + 1) (by omega) _)

theorem coeff_Gd (d n : ℕ) (hd : 1 ≤ d) :
    coeff n (Gd d) = if 0 < n ∧ d ∣ n then (d : ℤ) else 0 := by
  unfold Gd
  rw [← map_natCast (C (R := ℤ)) d, mul_assoc, coeff_C_mul, coeff_X_pow_mul']
  simp only [Wd, coeff_mk]
  by_cases h1 : d ≤ n
  · simp only [h1, ↓reduceIte]
    have hiff : d ∣ n - d ↔ (0 < n ∧ d ∣ n) := by
      constructor
      · intro h; refine ⟨by omega, ?_⟩
        have := Nat.dvd_add h (dvd_refl d); rwa [Nat.sub_add_cancel h1] at this
      · rintro ⟨_, h⟩; exact Nat.dvd_sub h (dvd_refl d)
    by_cases h2 : 0 < n ∧ d ∣ n
    · simp [h2, hiff.mpr h2]
    · have h3 : ¬ d ∣ n - d := fun h => h2 (hiff.mp h)
      simp only [h2, h3, ↓reduceIte, mul_zero]
  · have h2 : ¬ (0 < n ∧ d ∣ n) := fun ⟨h0, h⟩ => h1 (Nat.le_of_dvd h0 h)
    simp only [h1, h2, ↓reduceIte, mul_zero]

theorem coeff_EB (c : ℕ → ℤ) (D n : ℕ) (hn : 1 ≤ n) (hD : n ≤ D) :
    coeff n (EB c D) = ∑ d ∈ n.divisors, (d : ℤ) * c d := by
  unfold EB
  rw [map_sum]
  simp_rw [← map_intCast (C (R := ℤ)), coeff_C_mul]
  rw [Finset.sum_congr rfl (fun x _ => by rw [coeff_Gd (x + 1) n (by omega)])]
  simp_rw [mul_ite, mul_zero]
  rw [← Finset.sum_filter]
  refine Finset.sum_bij' (fun x _ => x + 1) (fun d _ => d - 1) ?_ ?_ ?_ ?_ ?_
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_range] at hx
    simp only [Nat.mem_divisors]
    exact ⟨hx.2.2, by omega⟩
  · intro d hd
    simp only [Nat.mem_divisors] at hd
    have := Nat.le_of_dvd (by omega) hd.1
    have h1 : 1 ≤ d := Nat.pos_of_dvd_of_pos hd.1 (by omega)
    simp only [Finset.mem_filter, Finset.mem_range]
    refine ⟨by omega, by omega, ?_⟩
    rw [Nat.sub_add_cancel h1]; exact hd.1
  · intro x _; simp
  · intro d hd
    simp only [Nat.mem_divisors] at hd
    have h1 : 1 ≤ d := Nat.pos_of_dvd_of_pos hd.1 (by omega)
    omega
  · intro x _; push_cast; ring


/-! ## exp(Σ b_n x^n / n) and its coefficients -/

/-- Coefficients of `exp (∑_{n ≥ 1} b n * x^n / n)`: the unique series `A` with `A 0 = 1` and
`x A' = (∑ b n x^n) A`, i.e. `(n+1) A_{n+1} = ∑_{j=0}^{n} b (j+1) A_{n-j}`. -/
def expCoeff (b : ℕ → ℤ) : ℕ → ℚ
  | 0 => 1
  | n + 1 => (∑ j : Fin (n + 1), (b (j + 1) : ℚ) * expCoeff b (n - j)) / (n + 1)
decreasing_by omega

theorem LD_rec (f B : ℤ⟦X⟧) (h : LD f B) (hf : constantCoeff f = 1) (n : ℕ) :
    ((n + 1 : ℕ) : ℤ) * coeff (n + 1) f =
      ∑ j ∈ Finset.range (n + 1), coeff (j + 1) B * coeff (n - j) f := by
  have h0 : coeff 0 B = 0 := by
    have := congrArg (coeff 0) h
    rw [coeff_theta, coeff_zero_eq_constantCoeff_apply, coeff_zero_eq_constantCoeff_apply,
      map_mul, hf, ← coeff_zero_eq_constantCoeff_apply] at this
    simpa using this.symm
  have := congrArg (coeff (n + 1)) h
  rw [coeff_theta, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Finset.sum_range_succ'] at this
  simp only [h0, zero_mul, add_zero] at this
  rw [this]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mem_range] at hj
  rw [show n + 1 - (j + 1) = n - j by omega]

theorem expCoeff_eq (b : ℕ → ℤ) (f B : ℤ⟦X⟧) (h : LD f B) (hf : constantCoeff f = 1) (D : ℕ)
    (hB : ∀ j, 1 ≤ j → j ≤ D → coeff j B = b j) : ∀ n, n ≤ D → expCoeff b n = coeff n f := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    rcases n with _ | n
    · simp [expCoeff, coeff_zero_eq_constantCoeff_apply, hf]
    · rw [expCoeff]
      have hr := LD_rec f B h hf n
      have hq : ((n + 1 : ℕ) : ℚ) * ((coeff (n + 1) f : ℤ) : ℚ) =
          ∑ j ∈ Finset.range (n + 1), ((coeff (j + 1) B : ℤ) : ℚ) * ((coeff (n - j) f : ℤ) : ℚ) := by
        exact_mod_cast hr
      rw [Fin.sum_univ_eq_sum_range (fun j => (b (j + 1) : ℚ) * expCoeff b (n - j)) (n + 1)]
      have hsum : ∑ j ∈ Finset.range (n + 1), (b (j + 1) : ℚ) * expCoeff b (n - j) =
          ∑ j ∈ Finset.range (n + 1), ((coeff (j + 1) B : ℤ) : ℚ) * ((coeff (n - j) f : ℤ) : ℚ) :=
        Finset.sum_congr rfl (fun j hj => by
          rw [Finset.mem_range] at hj
          rw [ih (n - j) (by omega) (by omega), hB (j + 1) (by omega) (by omega)])
      rw [hsum, ← hq]
      push_cast
      field_simp

theorem expCoeff_int_of_euler (b c : ℕ → ℤ)
    (h : ∀ n, 1 ≤ n → b n = ∑ d ∈ n.divisors, (d : ℤ) * c d) (n : ℕ) :
    ∃ z : ℤ, expCoeff b n = z :=
  ⟨coeff n (EP c n), expCoeff_eq b _ _ (LD_EP c n) (const_EP c n) n
    (fun j h1 h2 => by rw [coeff_EB c n j h1 h2, h j h1]) n le_rfl⟩

/-! ## Gauss congruences give an Euler product (Dwork) -/

/-- local Gauss congruence at `p` -/
def LGp (p : ℕ) (b : ℕ → ℤ) : Prop :=
  ∀ a m, 1 ≤ a → ((p : ℤ) ^ a) ∣ b (m * p ^ a) - b (m * p ^ (a - 1))

def cOf (b : ℕ → ℤ) (n : ℕ) : ℤ :=
  if n = 0 then 0 else (b n - ∑ d ∈ n.properDivisors.attach, (d.1 : ℤ) * cOf b d.1) / n
termination_by n
decreasing_by exact (Nat.mem_properDivisors.mp d.2).2

theorem cOf_eq (b : ℕ → ℤ) (n : ℕ) (hn : n ≠ 0) :
    cOf b n = (b n - ∑ d ∈ n.properDivisors, (d : ℤ) * cOf b d) / n := by
  rw [cOf]
  simp only [hn, ↓reduceIte]
  congr 2
  exact Finset.sum_attach n.properDivisors (fun d => (d : ℤ) * cOf b d)

theorem dvd_of_prime_pows (n : ℕ) (hn : n ≠ 0) (X : ℤ)
    (h : ∀ p : ℕ, p.Prime → ((p : ℤ) ^ n.factorization p) ∣ X) : (n : ℤ) ∣ X := by
  by_cases hX : X = 0
  · rw [hX]; exact dvd_zero _
  have hX' : X.natAbs ≠ 0 := by simpa using hX
  rw [Int.ofNat_dvd_left]
  apply (Nat.factorization_prime_le_iff_dvd hn hX').mp
  intro p hp
  have := h p hp
  rw [← Int.natCast_pow, Int.ofNat_dvd_left] at this
  exact (hp.pow_dvd_iff_le_factorization hX').mp this

theorem pow_dvd_of_not_dvd (p v m d : ℕ) (hp : p.Prime) (hv : 1 ≤ v) (hm : ¬ p ∣ m)
    (hd : d ∣ m * p ^ v) (hnd : ¬ d ∣ m * p ^ (v - 1)) : p ^ v ∣ d := by
  have hd0 : d ≠ 0 := by
    rintro rfl
    have h1 := Nat.eq_zero_of_zero_dvd hd
    have hpv : p ^ v ≠ 0 := pow_ne_zero _ hp.ne_zero
    have hm0 : m = 0 := by
      rcases Nat.mul_eq_zero.mp h1 with h | h
      · exact h
      · exact absurd h hpv
    exact hnd (by rw [hm0, zero_mul])
  obtain ⟨e, d', hpd', rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hd0 p hp.one_lt.ne'
  have hcop : Nat.Coprime (p ^ v) d' := (Nat.Coprime.pow_left v ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpd'))
  have hd'm : d' ∣ m := by
    have : d' ∣ m * p ^ v := Dvd.dvd.trans (Dvd.intro_left _ rfl) hd
    exact (Nat.Coprime.dvd_of_dvd_mul_right hcop.symm this)
  have hem : p ^ e ∣ p ^ v := by
    have : p ^ e ∣ m * p ^ v := Dvd.dvd.trans (Dvd.intro _ rfl) hd
    have hc2 : Nat.Coprime (p ^ e) m := Nat.Coprime.pow_left e ((Nat.Prime.coprime_iff_not_dvd hp).mpr hm)
    exact hc2.dvd_of_dvd_mul_left this
  have hle : e ≤ v := (Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp hem
  by_cases hev : e = v
  · subst hev; exact Dvd.intro _ rfl
  · exfalso; apply hnd
    have : p ^ e ∣ p ^ (v - 1) := Nat.pow_dvd_pow p (by omega)
    rw [mul_comm m]
    exact mul_dvd_mul this hd'm

theorem dwork (b : ℕ → ℤ) (hLG : ∀ p : ℕ, p.Prime → LGp p b) :
    ∀ n, 1 ≤ n → b n = ∑ d ∈ n.divisors, (d : ℤ) * cOf b d := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    set S := ∑ d ∈ n.properDivisors, (d : ℤ) * cOf b d with hS
    have hdvd : (n : ℤ) ∣ b n - S := by
      apply dvd_of_prime_pows n (by omega)
      intro p hp
      set v := n.factorization p with hv
      by_cases hv0 : v = 0
      · rw [hv0, pow_zero]; exact one_dvd _
      set m := n / p ^ v with hm
      have hnm : n = m * p ^ v := by
        rw [hm, hv, mul_comm]; exact (Nat.ordProj_mul_ordCompl_eq_self n p).symm
      have hpm : ¬ p ∣ m := Nat.not_dvd_ordCompl hp (by omega)
      set n' := m * p ^ (v - 1) with hn'
      have hn'n : n' ∣ n := by
        rw [hnm]; exact mul_dvd_mul_left m (Nat.pow_dvd_pow p (by omega))
      have hm0 : 1 ≤ m := by
        rcases Nat.eq_zero_or_pos m with h | h
        · rw [h] at hnm; omega
        · exact h
      have hn'lt : n' < n := by
        rw [hnm, hn']
        have : p ^ (v - 1) < p ^ v := Nat.pow_lt_pow_right hp.one_lt (by omega)
        exact Nat.mul_lt_mul_of_pos_left this (by omega)
      have hIH := ih n' hn'lt (by
        have : 1 ≤ p ^ (v - 1) := Nat.one_le_pow _ _ hp.pos
        rw [hn']; nlinarith)
      have hsub : n'.divisors ⊆ n.properDivisors := by
        intro d hd
        rw [Nat.mem_divisors] at hd
        rw [Nat.mem_properDivisors]
        exact ⟨hd.1.trans hn'n, lt_of_le_of_lt (Nat.le_of_dvd (by omega) hd.1) hn'lt⟩
      have hsplit := Finset.sum_sdiff hsub (f := fun d : ℕ => (d : ℤ) * cOf b d)
      have hX : b n - S = (b (m * p ^ v) - b (m * p ^ (v - 1))) -
          ∑ d ∈ (n.properDivisors \ n'.divisors : Finset ℕ), (d : ℤ) * cOf b d := by
        rw [hS, ← hsplit, ← hIH, ← hnm, hn']; ring
      rw [hX]
      apply dvd_sub (hLG p hp v m (by omega))
      apply Finset.dvd_sum
      intro d hd
      rw [Finset.mem_sdiff, Nat.mem_properDivisors, Nat.mem_divisors] at hd
      apply dvd_mul_of_dvd_left
      have := pow_dvd_of_not_dvd p v m d hp (by omega) hpm (by rw [← hnm]; exact hd.1.1)
        (fun h => hd.2 ⟨h, by rw [hn']; exact Nat.ne_of_gt (Nat.mul_pos hm0 (pow_pos hp.pos _))⟩)
      exact_mod_cast this
    rw [← Nat.insert_self_properDivisors (by omega : n ≠ 0),
      Finset.sum_insert Nat.self_notMem_properDivisors, ← hS, cOf_eq b n (by omega)]
    rw [Int.mul_ediv_cancel' hdvd]; ring

/-! ## closure of the local Gauss congruence -/

theorem LGp_mul {p : ℕ} {f g : ℕ → ℤ} (hf : LGp p f) (hg : LGp p g) : LGp p (fun n => f n * g n) := by
  intro a m ha
  have e : f (m * p ^ a) * g (m * p ^ a) - f (m * p ^ (a - 1)) * g (m * p ^ (a - 1)) =
      f (m * p ^ a) * (g (m * p ^ a) - g (m * p ^ (a - 1))) +
      (f (m * p ^ a) - f (m * p ^ (a - 1))) * g (m * p ^ (a - 1)) := by ring
  simp only; rw [e]
  exact dvd_add (dvd_mul_of_dvd_right (hg a m ha) _) (dvd_mul_of_dvd_left (hf a m ha) _)

theorem LGp_pow {p : ℕ} {f : ℕ → ℤ} (hf : LGp p f) (k : ℕ) : LGp p (fun n => f n ^ k) := by
  induction k with
  | zero => intro a m _; simp
  | succ k ih =>
    have := LGp_mul ih hf
    simpa [pow_succ] using this


/-! ## Fermat-Euler -/

theorem fermat_int (p : ℕ) (hp : p.Prime) (x : ℤ) : (p : ℤ) ∣ x ^ p - x := by
  have := Fact.mk hp
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rw [ZMod.pow_card, sub_self]

/-- Fermat-Euler: p^a ∣ x^(m p^a) - x^(m p^(a-1)). -/
theorem pow_gauss (p : ℕ) (hp : p.Prime) (x : ℤ) (a m : ℕ) (ha : 1 ≤ a) :
    ((p : ℤ) ^ a) ∣ x ^ (m * p ^ a) - x ^ (m * p ^ (a - 1)) := by
  obtain ⟨k, rfl⟩ : ∃ k, a = k + 1 := ⟨a - 1, by omega⟩
  have h := dvd_sub_pow_of_dvd_sub (fermat_int p hp (x ^ m)) k
  rw [← pow_mul, ← pow_mul, ← pow_mul, ← mul_assoc] at h
  rw [show k + 1 - 1 = k by omega, show m * p ^ (k + 1) = m * p * p ^ k by ring]
  exact h


/-! ## More closure properties of the Gauss congruences -/

theorem LGp_add {p : ℕ} {f g : ℕ → ℤ} (hf : LGp p f) (hg : LGp p g) :
    LGp p (fun n => f n + g n) := by
  intro a m ha
  have e : f (m * p ^ a) + g (m * p ^ a) - (f (m * p ^ (a - 1)) + g (m * p ^ (a - 1))) =
      (f (m * p ^ a) - f (m * p ^ (a - 1))) + (g (m * p ^ a) - g (m * p ^ (a - 1))) := by ring
  simp only; rw [e]; exact dvd_add (hf a m ha) (hg a m ha)

theorem LGp_neg {p : ℕ} {f : ℕ → ℤ} (hf : LGp p f) : LGp p (fun n => -f n) := by
  intro a m ha
  have e : -f (m * p ^ a) - -f (m * p ^ (a - 1)) = -(f (m * p ^ a) - f (m * p ^ (a - 1))) := by
    ring
  simp only; rw [e]; exact (hf a m ha).neg_right

theorem LGp_sub {p : ℕ} {f g : ℕ → ℤ} (hf : LGp p f) (hg : LGp p g) :
    LGp p (fun n => f n - g n) := by
  simpa [sub_eq_add_neg] using LGp_add hf (LGp_neg hg)

theorem LGp_const (p : ℕ) (z : ℤ) : LGp p (fun _ => z) := by
  intro a m _; simp

/-- Finite sums of Gauss sequences. -/
theorem LGp_sum {p : ℕ} {ι : Type*} (s : Finset ι) (f : ι → ℕ → ℤ)
    (hf : ∀ i ∈ s, LGp p (f i)) : LGp p (fun n => ∑ i ∈ s, f i n) := by
  intro a m ha
  rw [← Finset.sum_sub_distrib]
  exact Finset.dvd_sum (fun i hi => hf i hi a m ha)

/-- The subsequence `j ↦ b (j k)` of a Gauss sequence is a Gauss sequence. -/
theorem LGp_comp_mul {p : ℕ} {f : ℕ → ℤ} (hf : LGp p f) (k : ℕ) :
    LGp p (fun j => f (j * k)) := by
  intro a m ha
  have := hf a (m * k) ha
  simp only
  rwa [show m * p ^ a * k = m * k * p ^ a by ring,
    show m * p ^ (a - 1) * k = m * k * p ^ (a - 1) by ring]

/-- `j ↦ x ^ j` is a Gauss sequence (Fermat-Euler). -/
theorem LGp_zpow (p : ℕ) (hp : p.Prime) (x : ℤ) : LGp p (fun j => x ^ j) :=
  fun a m ha => pow_gauss p hp x a m ha

/-- If `u` is a Gauss sequence then so is `j ↦ u j ^ (j c)`. -/
theorem LGp_pow_self (p : ℕ) (hp : p.Prime) {u : ℕ → ℤ} (hu : LGp p u) (c : ℕ) :
    LGp p (fun j => u j ^ (j * c)) := by
  intro a m ha
  simp only
  set N := m * p ^ a
  set M := m * p ^ (a - 1)
  have h1 : (p : ℤ) ^ a ∣ u N ^ (N * c) - u M ^ (N * c) :=
    (hu a m ha).trans (sub_dvd_pow_sub_pow _ _ _)
  have h2 : (p : ℤ) ^ a ∣ u M ^ (N * c) - u M ^ (M * c) := by
    have := pow_gauss p hp (u M ^ c) a m ha
    rwa [← pow_mul, ← pow_mul, mul_comm c, mul_comm c] at this
  have e : u N ^ (N * c) - u M ^ (M * c) =
      (u N ^ (N * c) - u M ^ (N * c)) + (u M ^ (N * c) - u M ^ (M * c)) := by ring
  rw [e]; exact dvd_add h1 h2

/-- Conversely, an Euler-product sequence `b n = ∑_{d ∣ n} d c d` satisfies the Gauss
congruences at every prime. -/
theorem LGp_of_euler (b c : ℕ → ℤ) (h : ∀ n, 1 ≤ n → b n = ∑ d ∈ n.divisors, (d : ℤ) * c d)
    (p : ℕ) (hp : p.Prime) : LGp p b := by
  intro a m ha
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  set v := m.factorization p
  set m' := m / p ^ v
  have hmm : m = m' * p ^ v := by rw [mul_comm]; exact (Nat.ordProj_mul_ordCompl_eq_self m p).symm
  have hpm : ¬ p ∣ m' := Nat.not_dvd_ordCompl hp (by omega)
  have e1 : m * p ^ a = m' * p ^ (a + v) := by rw [hmm, pow_add]; ring
  have e2 : m * p ^ (a - 1) = m' * p ^ (a + v - 1) := by
    rw [hmm, show a + v - 1 = (a - 1) + v by omega, pow_add]; ring
  have hp0 : 0 < p := hp.pos
  have hsub : (m * p ^ (a - 1)).divisors ⊆ (m * p ^ a).divisors :=
    Nat.divisors_subset_of_dvd (by positivity) (mul_dvd_mul_left m (Nat.pow_dvd_pow p (by omega)))
  rw [h _ (Nat.succ_le_of_lt (by positivity)), h _ (Nat.succ_le_of_lt (by positivity)),
    ← Finset.sum_sdiff hsub, add_sub_cancel_right]
  apply Finset.dvd_sum
  intro d hd
  rw [Finset.mem_sdiff, Nat.mem_divisors, Nat.mem_divisors] at hd
  have h1 : d ∣ m' * p ^ (a + v) := by rw [← e1]; exact hd.1.1
  have h2 : ¬ d ∣ m' * p ^ (a + v - 1) := by
    rw [← e2]; exact fun h' => hd.2 ⟨h', by positivity⟩
  have := pow_dvd_of_not_dvd p (a + v) m' d hp (by omega) hpm h1 h2
  apply dvd_mul_of_dvd_left
  exact_mod_cast (Nat.pow_dvd_pow p (by omega : a ≤ a + v)).trans this

/-- Dwork's lemma, in the form used by the instances: Gauss congruences at every prime make
`exp (∑ b n x^n / n)` an integer series. -/
theorem expCoeff_int_of_gauss (b : ℕ → ℤ) (hLG : ∀ p : ℕ, p.Prime → LGp p b) (n : ℕ) :
    ∃ z : ℤ, expCoeff b n = z :=
  expCoeff_int_of_euler b (cOf b) (dwork b hLG) n

/-! ## The recurrence for `expCoeff` -/

theorem expCoeff_zero (b : ℕ → ℤ) : expCoeff b 0 = 1 := by rw [expCoeff]

theorem expCoeff_succ (b : ℕ → ℤ) (n : ℕ) :
    ((n : ℚ) + 1) * expCoeff b (n + 1) =
      ∑ j ∈ Finset.range (n + 1), (b (j + 1) : ℚ) * expCoeff b (n - j) := by
  rw [expCoeff, Fin.sum_univ_eq_sum_range (fun j => (b (j + 1) : ℚ) * expCoeff b (n - j)) (n + 1)]
  have : ((n : ℚ) + 1) ≠ 0 := by positivity
  field_simp

/-- `expCoeff b n` only depends on `b 1, ..., b n`. -/
theorem expCoeff_congr (b b' : ℕ → ℤ) (N : ℕ) (h : ∀ j, 1 ≤ j → j ≤ N → b j = b' j) :
    ∀ n, n ≤ N → expCoeff b n = expCoeff b' n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    rcases n with _ | n
    · rw [expCoeff_zero, expCoeff_zero]
    · have e1 := expCoeff_succ b n
      have e2 := expCoeff_succ b' n
      have hs : ∑ j ∈ Finset.range (n + 1), (b (j + 1) : ℚ) * expCoeff b (n - j) =
          ∑ j ∈ Finset.range (n + 1), (b' (j + 1) : ℚ) * expCoeff b' (n - j) :=
        Finset.sum_congr rfl (fun j hj => by
          rw [Finset.mem_range] at hj
          rw [h (j + 1) (by omega) (by omega), ih (n - j) (by omega) (by omega)])
      have hne : ((n : ℚ) + 1) ≠ 0 := by positivity
      have := e1.trans (hs.trans e2.symm)
      exact mul_left_cancel₀ hne this

/-- A sequence satisfying the `expCoeff` recurrence up to `N` agrees with `expCoeff` up to `N`. -/
theorem eq_expCoeff_of_rec (b : ℕ → ℤ) (A : ℕ → ℚ) (N : ℕ) (h0 : A 0 = 1)
    (h : ∀ n, n + 1 ≤ N →
      ((n : ℚ) + 1) * A (n + 1) = ∑ j ∈ Finset.range (n + 1), (b (j + 1) : ℚ) * A (n - j)) :
    ∀ n, n ≤ N → A n = expCoeff b n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    rcases n with _ | n
    · rw [h0, expCoeff_zero]
    · have e1 := h n hn
      have e2 := expCoeff_succ b n
      have hs : ∑ j ∈ Finset.range (n + 1), (b (j + 1) : ℚ) * A (n - j) =
          ∑ j ∈ Finset.range (n + 1), (b (j + 1) : ℚ) * expCoeff b (n - j) :=
        Finset.sum_congr rfl (fun j hj => by
          rw [Finset.mem_range] at hj
          rw [ih (n - j) (by omega) (by omega)])
      have hne : ((n : ℚ) + 1) ≠ 0 := by positivity
      exact mul_left_cancel₀ hne (e1.trans (hs.trans e2.symm))

/-! ## Converse: an integer exp series has Gauss congruences -/

theorem LD_of_expCoeff (b z : ℕ → ℤ) (hz : ∀ k, expCoeff b k = z k) :
    LD (PowerSeries.mk z) (PowerSeries.mk fun k => if k = 0 then 0 else b k) := by
  unfold LD
  ext n
  rw [coeff_theta, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  rcases n with _ | n
  · simp
  · rw [Finset.sum_range_succ']
    simp only [coeff_mk, ↓reduceIte, zero_mul, add_zero, Nat.add_eq_zero_iff, one_ne_zero,
      and_false]
    have h := expCoeff_succ b n
    simp only [hz] at h
    have h2 : (((n + 1 : ℕ) : ℤ) * z (n + 1) : ℤ) =
        ∑ j ∈ Finset.range (n + 1), b (j + 1) * z (n - j) := by exact_mod_cast h
    rw [h2]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mem_range] at hj
    rw [show n + 1 - (j + 1) = n - j by omega]

/-- An integer series `exp (∑ b n x^n / n)` has `b n = ∑_{d ∣ n} d * cOf b d` (converse of
`expCoeff_int_of_euler`). -/
theorem euler_of_expCoeff_int (b : ℕ → ℤ) (hF : ∀ n, ∃ z : ℤ, expCoeff b n = z) :
    ∀ n, 1 ≤ n → b n = ∑ d ∈ n.divisors, (d : ℤ) * cOf b d := by
  set z : ℕ → ℤ := fun k => (hF k).choose
  have hz : ∀ k, expCoeff b k = z k := fun k => (hF k).choose_spec
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    set S := ∑ d ∈ n.properDivisors, (d : ℤ) * cOf b d with hS
    set c' : ℕ → ℤ := fun d => if d < n then -cOf b d else 0
    set Q := PowerSeries.mk z * EP c' n
    set BQ := (PowerSeries.mk fun k => if k = 0 then 0 else b k) + EB c' n
    have hLD : LD Q BQ := LD_mul (LD_of_expCoeff b z hz) (LD_EP c' n)
    have hQ0 : constantCoeff Q = 1 := by
      simp only [Q, map_mul, const_EP, mul_one]
      rw [← coeff_zero_eq_constantCoeff_apply, coeff_mk]
      have := hz 0
      rw [expCoeff_zero] at this
      exact_mod_cast this.symm
    have hBQ : ∀ j, 1 ≤ j → j ≤ n →
        PowerSeries.coeff j BQ = b j - ∑ d ∈ j.divisors, (d : ℤ) * (if d < n then cOf b d else 0) := by
      intro j h1 h2
      simp only [BQ, map_add, coeff_mk, show j ≠ 0 by omega, ↓reduceIte]
      rw [coeff_EB c' n j h1 h2, sub_eq_add_neg, ← Finset.sum_neg_distrib]
      congr 1
      apply Finset.sum_congr rfl
      intro d _
      simp only [c']
      split_ifs <;> ring
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    have hrec := LD_rec Q BQ hLD hQ0 n'
    rw [Finset.sum_range_succ, Finset.sum_eq_zero, zero_add, Nat.sub_self,
      coeff_zero_eq_constantCoeff_apply, hQ0, mul_one, hBQ (n' + 1) (by omega) le_rfl] at hrec
    · have hsplit : ∑ d ∈ (n' + 1).divisors, (d : ℤ) * (if d < n' + 1 then cOf b d else 0) = S := by
        rw [← Nat.cons_self_properDivisors (by omega), Finset.sum_cons]
        simp only [lt_irrefl, ↓reduceIte, mul_zero, zero_add, hS]
        apply Finset.sum_congr rfl
        intro d hd
        simp [(Nat.mem_properDivisors.mp hd).2]
      rw [hsplit] at hrec
      have hdvd : ((n' + 1 : ℕ) : ℤ) ∣ b (n' + 1) - S := ⟨_, hrec.symm⟩
      rw [← Nat.insert_self_properDivisors (by omega : n' + 1 ≠ 0),
        Finset.sum_insert Nat.self_notMem_properDivisors, ← hS, cOf_eq b (n' + 1) (by omega),
        Int.mul_ediv_cancel' hdvd]
      ring
    · intro j hj
      rw [Finset.mem_range] at hj
      rw [hBQ (j + 1) (by omega) (by omega)]
      have : ∑ d ∈ (j + 1).divisors, (d : ℤ) * (if d < n' + 1 then cOf b d else 0) =
          ∑ d ∈ (j + 1).divisors, (d : ℤ) * cOf b d := by
        apply Finset.sum_congr rfl
        intro d hd
        have := Nat.le_of_dvd (by omega) (Nat.mem_divisors.mp hd).1
        have h' : d < n' + 1 := by omega
        simp [h']
      rw [this, ← ih (j + 1) (by omega) (by omega), sub_self, zero_mul]

/-- If `exp (∑ b n x^n / n)` is an integer series, `b` satisfies the Gauss congruences. -/
theorem gauss_of_expCoeff_int (b : ℕ → ℤ) (hF : ∀ n, ∃ z : ℤ, expCoeff b n = z)
    (p : ℕ) (hp : p.Prime) : LGp p b :=
  LGp_of_euler b (cOf b) (euler_of_expCoeff_int b hF) p hp

end OpenProblemsLib.Dwork
