import Mathlib

/-
OEIS A181316 (P. D. Hanna, 2010): g.f. exp(Σ_{n≥1} 2((3^n-1)/2)^(n-1) x^n/n).
Conjecture: exp(Σ_{n≥1} (q-1)((q^n-1)/(q-1))^(n-1) x^n/n) is an integer series for all
integers q > 1.

Definitions.
* `bq q n = (q-1) * ((q^n - 1)/(q - 1))^(n-1)` (ℤ division, exact; `div_eq_c`).
* `c q n = 1 + q + ... + q^(n-1)`.
* `expCoeff b n`: coefficients of exp(Σ b(n) x^n/n), given by A(0) = 1 and
  (n+1) A(n+1) = Σ_{j=0..n} b(j+1) A(n-j), over ℚ.

Main theorems.
* `A181316_conjecture (q) (2 ≤ q) n : ∃ z : ℤ, expCoeff (bq q) n = z`.
* `A181316_int`: the case q = 3 (the entry's own series).

Route.
* `LG_b`: the Gauss congruence b(m p^a) ≡ b(m p^(a-1)) (mod p^a) for every prime p, with
  N = M p: if p ∤ c(M) and p ∤ q-1, then c(N) ≡ c(M) (from q^N ≡ q^M, `pow_gauss`) and
  c(M)^(N-M) ≡ 1 (mod p^a); if p ∤ c(M) and p | q-1, then p ∤ M, so a = 1 and both terms are
  ≡ 0 (mod p); if p | c(M) (then p | c(N), `c_split`), both terms are ≡ 0 (mod p^a) by size of
  the exponents, except p = 2, a = 2, M = 2, where 4 | (q-1)(q+1).
* `dwork`, `expCoeff_int_of_euler` (Gauss congruences give an Euler product
  Π (1 - x^d)^(-c(d)) with integer exponents): copied from OEIS/A207969/A207969_mathlib.lean.
Not checked here: that `expCoeff` is the OEIS "exp(...)" (the recurrence is the standard
characterisation); the data match is checked by certificate/check.py only.
-/

namespace A181316

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


/-! ## the sequence (q-1) [n]_q^(n-1) -/

/-- `c q n = 1 + q + ... + q^(n-1)`. -/
def c (q : ℤ) (n : ℕ) : ℤ := ∑ i ∈ Finset.range n, q ^ i

/-- The OEIS summand: `b q n = (q-1) * ((q^n - 1)/(q - 1))^(n-1)`. -/
def bq (q : ℤ) (n : ℕ) : ℤ := (q - 1) * ((q ^ n - 1) / (q - 1)) ^ (n - 1)

theorem c_mul (q : ℤ) (n : ℕ) : c q n * (q - 1) = q ^ n - 1 := geom_sum_mul q n

theorem div_eq_c (q : ℤ) (hq : 2 ≤ q) (n : ℕ) : (q ^ n - 1) / (q - 1) = c q n := by
  rw [← c_mul]; exact Int.mul_ediv_cancel _ (by omega)

theorem bq_eq (q : ℤ) (hq : 2 ≤ q) (n : ℕ) : bq q n = (q - 1) * c q n ^ (n - 1) := by
  rw [bq, div_eq_c q hq]

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

theorem c_split (q : ℤ) (hq : 2 ≤ q) (M p : ℕ) : c q (M * p) = c q M * c (q ^ M) p := by
  have h1 := c_mul q (M * p)
  have h2 := c_mul q M
  have h3 := c_mul (q ^ M) p
  have hq1 : q - 1 ≠ 0 := by omega
  have h4 : (q ^ M) ^ p = q ^ (M * p) := (pow_mul q M p).symm
  apply mul_right_cancel₀ hq1
  linear_combination h1 - c (q ^ M) p * h2 - h3 - h4

theorem c_one (q : ℤ) : c q 1 = 1 := by simp [c]

theorem c_sub_self_dvd (q : ℤ) (M : ℕ) : (q - 1) ∣ c q M - M := by
  have : c q M - M = ∑ i ∈ Finset.range M, (q ^ i - 1) := by
    simp [c, Finset.sum_sub_distrib]
  rw [this]
  exact Finset.dvd_sum (fun i _ => by simpa using sub_dvd_pow_sub_pow q 1 i)

theorem two_pow_ge (a : ℕ) (ha : 3 ≤ a) : a + 1 ≤ 2 ^ (a - 1) := by
  induction a with
  | zero => omega
  | succ a ih =>
    rcases Nat.lt_or_ge a 3 with h | h
    · interval_cases a <;> simp_all
    · have := ih h
      rw [show a + 1 - 1 = (a - 1) + 1 by omega, pow_succ]; omega

theorem LG_b (q : ℤ) (hq : 2 ≤ q) (p : ℕ) (hp : p.Prime) :
    LGp p (fun n => (q - 1) * c q n ^ (n - 1)) := by
  intro a m ha
  simp only
  rcases Nat.eq_zero_or_pos m with hm0 | hm0
  · subst hm0; simp
  set M := m * p ^ (a - 1) with hMdef
  have hN : m * p ^ a = M * p := by
    rw [hMdef, mul_assoc, ← pow_succ, show a - 1 + 1 = a by omega]
  rw [hN]
  have hp2 := hp.two_le
  have hM1 : 1 ≤ M := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hMp : M ≤ M * p := Nat.le_mul_of_pos_right _ (by omega)
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hsplit := c_split q hq M p
  by_cases hc : (p : ℤ) ∣ c q M
  · have hcN : (p : ℤ) ∣ c q (M * p) := hsplit ▸ dvd_mul_of_dvd_left hc _
    have hM2 : 2 ≤ M := by
      by_contra h
      have : M = 1 := by omega
      rw [this, c_one] at hc
      exact hpz.not_dvd_one hc
    have hNa : a ≤ M * p - 1 := by
      have : a < p ^ a := Nat.lt_pow_self (by omega)
      have : p ^ a ≤ M * p := by rw [← hN]; exact Nat.le_mul_of_pos_left _ hm0
      omega
    have hbN : (p : ℤ) ^ a ∣ (q - 1) * c q (M * p) ^ (M * p - 1) :=
      dvd_mul_of_dvd_right ((pow_dvd_pow _ hNa).trans (pow_dvd_pow_of_dvd hcN _)) _
    have hbM : (p : ℤ) ^ a ∣ (q - 1) * c q M ^ (M - 1) := by
      by_cases hMa : a ≤ M - 1
      · exact dvd_mul_of_dvd_right ((pow_dvd_pow _ hMa).trans (pow_dvd_pow_of_dvd hc _)) _
      · -- the only case: p = 2, a = 2, M = 2
        have hpa : p ^ (a - 1) ≤ M := Nat.le_mul_of_pos_left _ hm0
        have hspec : p = 2 ∧ a = 2 ∧ M = 2 := by
          rcases Nat.lt_or_ge a 3 with h3 | h3
          · interval_cases a
            · omega
            · have hMle : M ≤ 2 := by omega
              have hmp : m * p = M := by rw [hMdef]; simp
              have hmle : m * 2 ≤ m * p := Nat.mul_le_mul_left m hp2
              have hm_1 : m = 1 := by nlinarith
              subst hm_1
              refine ⟨by omega, rfl, by omega⟩
          · have h1 := two_pow_ge a h3
            have h2 : 2 ^ (a - 1) ≤ p ^ (a - 1) := Nat.pow_le_pow_left hp2 _
            omega
        obtain ⟨rfl, rfl, hM⟩ := hspec
        rw [hM] at hc ⊢
        have hc2 : c q 2 = 1 + q := by simp [c, Finset.sum_range_succ]
        rw [hc2] at hc
        have h2 : (2 : ℤ) ∣ q - 1 := by
          have : q - 1 = (1 + q) - 2 := by ring
          rw [this]; exact dvd_sub (by exact_mod_cast hc) (dvd_refl _)
        rw [hc2]
        push_cast
        simpa [pow_two] using mul_dvd_mul h2 (show (2 : ℤ) ∣ (1 + q) ^ (2 - 1) by simpa using hc)
    exact dvd_sub hbN hbM
  · by_cases hq1 : (p : ℤ) ∣ q - 1
    · have ha1 : a = 1 := by
        by_contra h
        have hpM : (p : ℤ) ∣ (M : ℤ) := by
          rw [hMdef]; push_cast
          exact dvd_mul_of_dvd_right (dvd_pow_self _ (by omega)) _
        exact hc ((dvd_sub_comm.mp (hq1.trans (c_sub_self_dvd q M))) |> fun h => by
          have := dvd_sub hpM h; simpa using this)
      subst ha1
      rw [pow_one, ← mul_sub]
      exact dvd_mul_of_dvd_left hq1 _
    · have hcop1 : IsCoprime ((p : ℤ) ^ a) (q - 1) :=
        (hpz.coprime_iff_not_dvd.mpr hq1).pow_left
      have hcop2 : IsCoprime ((p : ℤ) ^ a) (c q M) :=
        (hpz.coprime_iff_not_dvd.mpr hc).pow_left
      have h1 : (p : ℤ) ^ a ∣ c q (M * p) - c q M := by
        have g := pow_gauss p hp q a m ha
        rw [hN, ← hMdef] at g
        have e : q ^ (M * p) - q ^ M = (c q (M * p) - c q M) * (q - 1) := by
          rw [sub_mul, c_mul, c_mul]; ring
        rw [e] at g
        exact hcop1.dvd_of_dvd_mul_right g
      have h2 : (p : ℤ) ^ a ∣ c q M ^ (M * p - M) - 1 := by
        have g := pow_gauss p hp (c q M) a m ha
        rw [hN, ← hMdef] at g
        have e : c q M ^ (M * p) - c q M ^ M = c q M ^ M * (c q M ^ (M * p - M) - 1) := by
          rw [mul_sub, ← pow_add, show M + (M * p - M) = M * p by omega]; ring
        rw [e] at g
        exact (hcop2.pow_right).dvd_of_dvd_mul_left g
      have e : (q - 1) * c q (M * p) ^ (M * p - 1) - (q - 1) * c q M ^ (M - 1) =
          (q - 1) * ((c q (M * p) ^ (M * p - 1) - c q M ^ (M * p - 1)) +
            c q M ^ (M - 1) * (c q M ^ (M * p - M) - 1)) := by
        rw [mul_sub (c q M ^ (M - 1)), ← pow_add, show M - 1 + (M * p - M) = M * p - 1 by omega]
        ring
      rw [e]
      exact dvd_mul_of_dvd_right (dvd_add (h1.trans (sub_dvd_pow_sub_pow _ _ _))
        (dvd_mul_of_dvd_right h2 _)) _

/-- The conjecture of A181316: exp(Σ (q-1) ((q^n-1)/(q-1))^(n-1) x^n/n) is an integer series
for every integer q ≥ 2. -/
theorem A181316_conjecture (q : ℤ) (hq : 2 ≤ q) (n : ℕ) : ∃ z : ℤ, expCoeff (bq q) n = z := by
  have hb : bq q = fun n => (q - 1) * c q n ^ (n - 1) := funext (bq_eq q hq)
  rw [hb]
  exact expCoeff_int_of_euler _ _ (dwork _ (fun p hp => LG_b q hq p hp)) n

/-- A181316 itself (q = 3): exp(Σ 2 ((3^n-1)/2)^(n-1) x^n/n) has integer coefficients. -/
theorem A181316_int (n : ℕ) : ∃ z : ℤ, expCoeff (bq 3) n = z := A181316_conjecture 3 (by norm_num) n
