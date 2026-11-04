/-
OEIS A061002, conjecture (G. Detlefs 2013): for the n-th prime p and H(m) the
m-th harmonic number, denominator(H(p)/H(p-1)) / numerator(H(p-1)/p^2) = p^3
(A193758(p)/a(n) = p^3 for p > 3).

Main theorem `A061002_conjecture`: for every prime p ≥ 5, with H = Mathlib's
`harmonic` (H m = Σ_{i=1}^m 1/i in ℚ), the denominator of H(p)/H(p-1) equals
p^3 times the numerator of H(p-1)/p^2, that numerator is positive, and so
den/num = p^3 in ℚ.  This is the README result.

Proof.  Wolstenholme's theorem is proved here (`wolstenholme`): with
F = (p-1)! and N = Σ_{k=1}^{p-1} F/k (so H(p-1) = N/F), pairing k with p-k
gives 2N = p·Σ_k G_k with G_k = F/(k(p-k)); by Wilson's theorem
G_k ≡ k^(-2) (mod p), and Σ_{x ∈ ZMod p} x^2 = 0 (Mathlib
`FiniteField.sum_pow_lt_card_sub_one`, p ≥ 5), so p^2 ∣ N and p^2 divides the
numerator a of H(p-1), while p ∤ b = its denominator (b ∣ F).  Then
H(p)/H(p-1) = (pa + b)/(pa) in lowest terms and H(p-1)/p^2 = (a/p^2)/b in
lowest terms.

Not checked: nothing outside Lean.
-/
import Mathlib

open Finset

lemma pair_dvd_factorial {p k : ℕ} (hk1 : 1 ≤ k) (hkp : k < p) (hne : k ≠ p - k) :
    k * (p - k) ∣ (p - 1).factorial := by
  have hF : (p - 1).factorial = ∏ x ∈ Ico 1 p, x := by
    rw [← Finset.prod_Ico_id_eq_factorial]; congr 2; omega
  have hpair : k * (p - k) = ∏ x ∈ ({k, p - k} : Finset ℕ), x := (Finset.prod_pair (f := fun x => x) hne).symm
  rw [hF, hpair]
  apply Finset.prod_dvd_prod_of_subset
  intro x hx
  simp only [mem_insert, mem_singleton] at hx
  simp only [mem_Ico]
  omega

lemma wolstenholme_nat {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) :
    p ^ 2 ∣ ∑ i ∈ range (p - 1), (p - 1).factorial / (i + 1) := by
  have := Fact.mk hp
  set F := (p - 1).factorial with hFdef
  set n := p - 1 with hn
  have hodd : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with h | h
    · omega
    · exact h
  -- G i = F / ((i+1)(p-(i+1)))
  set G : ℕ → ℕ := fun i => F / ((i + 1) * (p - (i + 1))) with hGdef
  have hG : ∀ i ∈ range n, F = (i + 1) * (p - (i + 1)) * G i := by
    intro i hi
    simp only [mem_range] at hi
    have := pair_dvd_factorial (p := p) (k := i + 1) (by omega) (by omega) (by omega)
    exact (Nat.mul_div_cancel' this).symm
  have hterm : ∀ i ∈ range n, F / (i + 1) + F / (p - (i + 1)) = p * G i := by
    intro i hi
    have hGi := hG i hi
    simp only [mem_range] at hi
    have e1 : F / (i + 1) = (p - (i + 1)) * G i :=
      Nat.div_eq_of_eq_mul_left (by omega) (by rw [hGi]; ring)
    have e2 : F / (p - (i + 1)) = (i + 1) * G i :=
      Nat.div_eq_of_eq_mul_left (by omega) (by rw [hGi]; ring)
    rw [e1, e2, ← add_mul]; congr 1; omega
  have hrefl : ∑ i ∈ range n, F / (p - (i + 1)) = ∑ i ∈ range n, F / (i + 1) := by
    rw [← Finset.sum_range_reflect (fun i => F / (i + 1)) n]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [mem_range] at hi
    congr 1; omega
  have h2N : 2 * ∑ i ∈ range n, F / (i + 1) = p * ∑ i ∈ range n, G i := by
    rw [two_mul]
    nth_rewrite 2 [← hrefl]
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    exact Finset.sum_congr rfl hterm
  -- p ∣ Σ G i, computed in ZMod p.
  have hS : p ∣ ∑ i ∈ range n, G i := by
    rw [← ZMod.natCast_eq_zero_iff]
    push_cast
    have hGz : ∀ i ∈ range n, ((G i : ℕ) : ZMod p) = (((i + 1 : ℕ) : ZMod p) ^ 2)⁻¹ := by
      intro i hi
      have hGi := hG i hi
      simp only [mem_range] at hi
      have hw : ((F : ℕ) : ZMod p) = -1 := by
        show (((p - 1).factorial : ℕ) : ZMod p) = -1
        exact ZMod.wilsons_lemma p
      rw [hGi] at hw
      push_cast [Nat.cast_sub (by omega : i + 1 ≤ p)] at hw
      rw [ZMod.natCast_self] at hw
      apply eq_inv_of_mul_eq_one_right
      push_cast
      linear_combination -hw
    rw [Finset.sum_congr rfl hGz]
    have hsum : ∑ i ∈ range n, (((i + 1 : ℕ) : ZMod p) ^ 2)⁻¹ =
        ∑ x : ZMod p, (x ^ 2)⁻¹ := by
      have hr : ∑ i ∈ range p, (((i : ℕ) : ZMod p) ^ 2)⁻¹ =
          ∑ i ∈ range n, (((i + 1 : ℕ) : ZMod p) ^ 2)⁻¹ := by
        have hrange : range p = range (n + 1) := by congr 1; omega
        rw [hrange, Finset.sum_range_succ']
        simp
      rw [← hr]
      apply Finset.sum_nbij (fun k : ℕ => (k : ZMod p))
      · intro a _; exact mem_univ _
      · intro a ha b hb hab
        simp only [coe_range, Set.mem_Iio] at ha hb
        have := congrArg ZMod.val hab
        simp only [ZMod.val_natCast] at this
        rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this
      · intro x _
        exact ⟨x.val, by simp [ZMod.val_lt], ZMod.natCast_zmod_val x⟩
      · intro a _; rfl
    rw [hsum]
    have hinv : ∑ x : ZMod p, (x ^ 2)⁻¹ = ∑ x : ZMod p, x ^ 2 := by
      simp only [← inv_pow]
      exact Equiv.sum_comp (Function.Involutive.toPerm (fun x : ZMod p => x⁻¹) inv_inv)
        (fun x => x ^ 2)
    rw [hinv]
    apply FiniteField.sum_pow_lt_card_sub_one
    rw [ZMod.card]; omega
  obtain ⟨t, ht⟩ := hS
  have : p ^ 2 ∣ 2 * ∑ i ∈ range n, F / (i + 1) := ⟨t, by rw [h2N, ht]; ring⟩
  have hcop : Nat.Coprime (p ^ 2) 2 := by
    apply Nat.Coprime.pow_left
    exact (Nat.coprime_primes hp Nat.prime_two).2 (by omega)
  exact hcop.dvd_of_dvd_mul_left this

lemma harmonic_eq_div (p : ℕ) :
    harmonic (p - 1) = ((∑ i ∈ range (p - 1), (p - 1).factorial / (i + 1) : ℕ) : ℚ) /
      ((p - 1).factorial : ℚ) := by
  have hF0 : ((p - 1).factorial : ℚ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  unfold harmonic
  rw [Nat.cast_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [mem_range] at hi
  have hd : i + 1 ∣ (p - 1).factorial := Nat.dvd_factorial (by omega) (by omega)
  rw [Nat.cast_div hd (by exact_mod_cast (Nat.succ_ne_zero i)), div_div_cancel_left' hF0]

/-- Wolstenholme: p^2 divides the numerator of H(p-1), and p does not divide
its denominator. -/
theorem wolstenholme {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) :
    (p : ℤ) ^ 2 ∣ (harmonic (p - 1)).num ∧ ¬ (p : ℤ) ∣ ((harmonic (p - 1)).den : ℤ) := by
  set q := harmonic (p - 1) with hqdef
  set F := (p - 1).factorial
  set N := ∑ i ∈ range (p - 1), (p - 1).factorial / (i + 1)
  have hq : q = (N : ℚ) / F := harmonic_eq_div p
  have hF0 : (F : ℚ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  have hkey : q.num * (F : ℤ) = (N : ℤ) * q.den := by
    have : (q.num : ℚ) * F = (N : ℚ) * q.den := by
      rw [← Rat.mul_den_eq_num, hq]; field_simp
    exact_mod_cast this
  have hpF : ¬ p ∣ F := by
    rw [Nat.Prime.dvd_factorial hp]; omega
  have hcopF : IsCoprime ((p : ℤ) ^ 2) (F : ℤ) := by
    have : Nat.Coprime (p ^ 2) F :=
      Nat.Coprime.pow_left 2 ((Nat.Prime.coprime_iff_not_dvd hp).2 hpF)
    exact_mod_cast Nat.isCoprime_iff_coprime.mpr this
  obtain ⟨c, hc⟩ := wolstenholme_nat hp h5
  refine ⟨?_, ?_⟩
  · apply hcopF.dvd_of_dvd_mul_right
    rw [hkey]
    exact Dvd.dvd.mul_right (by exact_mod_cast (⟨c, hc⟩ : p ^ 2 ∣ N)) _
  · intro hpd
    have hred : IsCoprime q.num (q.den : ℤ) := Int.isCoprime_iff_gcd_eq_one.mpr q.reduced
    have hbF : (q.den : ℤ) ∣ q.num * F := ⟨N, by rw [hkey]; ring⟩
    have hbF' : (q.den : ℤ) ∣ F := hred.symm.dvd_of_dvd_mul_left hbF
    have : (p : ℤ) ∣ F := dvd_trans hpd hbF'
    exact hpF (by exact_mod_cast this)

theorem A061002_conjecture (p : ℕ) (hp : p.Prime) (h5 : 5 ≤ p) :
    (((harmonic p / harmonic (p - 1)).den : ℤ) =
        (p : ℤ) ^ 3 * (harmonic (p - 1) / (p : ℚ) ^ 2).num) ∧
      0 < (harmonic (p - 1) / (p : ℚ) ^ 2).num ∧
      ((harmonic p / harmonic (p - 1)).den : ℚ) / (harmonic (p - 1) / (p : ℚ) ^ 2).num
        = (p : ℚ) ^ 3 := by
  obtain ⟨⟨c, hc⟩, hpb⟩ := wolstenholme hp h5
  set q := harmonic (p - 1) with hqdef
  set a := q.num
  set b : ℤ := (q.den : ℤ)
  have hqpos : 0 < q := harmonic_pos (by omega)
  have ha : 0 < a := Rat.num_pos.mpr hqpos
  have hb : 0 < b := Nat.cast_pos.mpr q.den_pos
  have hp0 : (0 : ℤ) < p := by exact_mod_cast hp.pos
  have hqab : q = (a : ℚ) / b := (Rat.num_div_den q).symm
  have hHp : harmonic p = q + ((p : ℚ))⁻¹ := by
    have := harmonic_succ (p - 1)
    rw [show p - 1 + 1 = p by omega] at this
    rw [this]
  have hred : IsCoprime a b := Int.isCoprime_iff_gcd_eq_one.mpr q.reduced
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hbp : IsCoprime b (p : ℤ) :=
    ((Irreducible.coprime_iff_not_dvd hpz.irreducible).2 hpb).symm
  -- H(p)/H(p-1) = (pa + b)/(pa), in lowest terms.
  have hratio : harmonic p / q = ((p * a + b : ℤ) : ℚ) / ((p * a : ℤ) : ℚ) := by
    rw [hHp, hqab]
    have : (a : ℚ) ≠ 0 := by exact_mod_cast ha.ne'
    have : (b : ℚ) ≠ 0 := by exact_mod_cast hb.ne'
    have : (p : ℚ) ≠ 0 := by exact_mod_cast hp0.ne'
    push_cast
    field_simp
  have hcop1 : IsCoprime (p * a + b) (p * a) := by
    have h1 : IsCoprime (p * a + b) (p : ℤ) := by
      have := hbp.add_mul_left_left a; rwa [add_comm] at this
    have h2 : IsCoprime (p * a + b) a := by
      have := hred.symm.add_mul_left_left (p : ℤ)
      rwa [add_comm, mul_comm a] at this
    exact h1.mul_right h2
  have hden : ((harmonic p / q).den : ℤ) = p * a := by
    rw [hratio]
    exact Rat.den_div_eq_of_coprime (by positivity) (Int.isCoprime_iff_gcd_eq_one.mp hcop1)
  -- H(p-1)/p^2 = c/b, in lowest terms.
  have hcz : a = (p : ℤ) ^ 2 * c := hc
  have hc0 : 0 < c := by
    by_contra hneg; push Not at hneg
    have : a ≤ 0 := by rw [hcz]; exact mul_nonpos_of_nonneg_of_nonpos (by positivity) hneg
    omega
  have hq2 : q / (p : ℚ) ^ 2 = (c : ℚ) / (b : ℚ) := by
    rw [hqab, hcz]
    have : (p : ℚ) ≠ 0 := by exact_mod_cast hp0.ne'
    have : (b : ℚ) ≠ 0 := by exact_mod_cast hb.ne'
    push_cast; field_simp
  have hcop2 : IsCoprime c b := by
    have : IsCoprime ((p : ℤ) ^ 2 * c) b := by rw [← hcz]; exact hred
    exact this.of_mul_left_right
  have hnum : (q / (p : ℚ) ^ 2).num = c := by
    rw [hq2]
    exact Rat.num_div_eq_of_coprime hb (Int.isCoprime_iff_gcd_eq_one.mp hcop2)
  refine ⟨?_, ?_, ?_⟩
  · rw [hden, hnum, hcz]; ring
  · rw [hnum]; exact hc0
  · have h1 : ((harmonic p / q).den : ℚ) = (((harmonic p / q).den : ℤ) : ℚ) := by norm_cast
    rw [h1, hden, hnum, hcz]
    have : (c : ℚ) ≠ 0 := by exact_mod_cast hc0.ne'
    push_cast; field_simp
