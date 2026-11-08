import Mathlib
import OpenProblemsLib.PNTApps

/-
OEIS A200982.  k is a term iff k ∣ 1^L + 2^L + ... + (k-1)^L with L = lambda(k)/2,
lambda = Carmichael's function (`ArithmeticFunction.carmichael`, the exponent of (ZMod k)ˣ).
Conjecture in the entry: the terms have asymptotic density zero.

Checked here: the conjecture.
* `A200982_not_term_of_mixed`: if a prime p ≡ 1 (mod 4) and a prime q ≡ 3 (mod 4) both
  divide k, then k is not a term.  (q^(e-1)(q-1) divides L, so modulo q^e every j prime to q
  contributes 1 and every multiple of q contributes 0; the sum is ≡ (k/q)(q-1), of q-adic
  valuation e - 1, where q^e exactly divides k.)
* `A200982_density_zero`: the terms have natural density 0.  Every term avoids all primes
  ≡ 1 (mod 4) or all primes ≡ 3 (mod 4); both sets have density 0 by the sieve
  `density_zero_of_sieve` of OpenProblemsLib.PNTApps, fed by Dirichlet's divergence of the sum
  of 1/p over each class (`not_summable_one_div_prime_mod`).
Not checked here: the full characterisation of the terms (Grau, Oller-Marcén, Prop. 12); only
the necessary condition above is needed.  Axioms propext, Classical.choice, Quot.sound.
-/

namespace A200982

open ArithmeticFunction

/-- `k` is a term of A200982 (k ≥ 1). -/
def IsTerm (k : ℕ) : Prop := 1 ≤ k ∧ k ∣ ∑ j ∈ Finset.Ico 1 k, j ^ (carmichael k / 2)

/-- The primes `p ≡ r (mod 4)`. -/
def P4 (r : ℕ) : Set ℕ := {p | p.Prime ∧ p % 4 = r}

end A200982

open A200982 ArithmeticFunction Filter Topology Finset OpenProblemsLib.PNTApps

theorem A200982_not_term_of_mixed {k p q : ℕ} (hk : 0 < k) (hp : p.Prime) (hp4 : p % 4 = 1)
    (hq : q.Prime) (hq4 : q % 4 = 3) (hpk : p ∣ k) (hqk : q ∣ k) :
    ¬ k ∣ ∑ j ∈ Finset.Ico 1 k, j ^ (carmichael k / 2) := by
  intro hdiv
  set lam := carmichael k with hlam
  set e := k.factorization q
  set m := k / q ^ e
  have hkm : q ^ e * m = k := Nat.ordProj_mul_ordCompl_eq_self k q
  have hm : ¬ q ∣ m := Nat.not_dvd_ordCompl hq hk.ne'
  have he : 0 < e := hq.factorization_pos_of_dvd hk.ne' hqk
  have hq2 : q ≠ 2 := by rintro rfl; norm_num at hq4
  have hq3 : 3 ≤ q := by have := hq.two_le; omega
  have hphi : (q ^ e).totient = q ^ (e - 1) * (q - 1) := Nat.totient_prime_pow hq he
  have h1 : q ^ (e - 1) * (q - 1) ∣ lam := by
    rw [← hphi, ← carmichael_pow_of_prime_ne_two e hq hq2]
    exact carmichael_dvd ⟨m, hkm.symm⟩
  have h2 : p - 1 ∣ lam := by
    rw [← carmichael_of_prime hp]; exact carmichael_dvd hpk
  have h4 : 4 ∣ lam := ((Nat.dvd_iff_mod_eq_zero ..).mpr (by omega : (p - 1) % 4 = 0)).trans h2
  have hlam0 : lam ≠ 0 := by
    intro h
    have := carmichael_dvd_totient k
    rw [← hlam, h, zero_dvd_iff] at this
    exact (Nat.totient_pos.mpr hk).ne' this
  set L := lam / 2 with hLdef
  have hlamL : lam = 2 * L := (Nat.mul_div_cancel' ((by norm_num : 2 ∣ 4).trans h4)).symm
  have hL2 : 2 ∣ L := by
    rw [hlamL] at h4
    have h4' : 2 * 2 ∣ 2 * L := by norm_num; exact h4
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 2) h4'
  set u := (q - 1) / 2
  have hqu : q - 1 = 2 * u := by omega
  have hu : Odd u := by
    rw [Nat.odd_iff]; omega
  have hφL : q ^ (e - 1) * (q - 1) ∣ L := by
    rw [hqu]
    have hA : q ^ (e - 1) * u ∣ L := by
      have h1' := h1
      rw [hqu, hlamL, show q ^ (e - 1) * (2 * u) = 2 * (q ^ (e - 1) * u) by ring] at h1'
      exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) h1'
    have hco : Nat.Coprime 2 (q ^ (e - 1) * u) :=
      Nat.Coprime.mul_right (Nat.Coprime.pow_right _ ((Nat.coprime_primes Nat.prime_two hq).mpr
        (Ne.symm hq2))) (Nat.coprime_two_left.mpr hu)
    rw [show q ^ (e - 1) * (2 * u) = 2 * (q ^ (e - 1) * u) by ring]
    exact hco.mul_dvd_of_dvd_of_dvd hL2 hA
  have hLpos : 0 < L := by omega
  have heL : e ≤ L := by
    have a1 : e - 1 < q ^ (e - 1) := Nat.lt_pow_self (by omega)
    have a2 : q ^ (e - 1) ≤ q ^ (e - 1) * (q - 1) := Nat.le_mul_of_pos_right _ (by omega)
    have a3 := Nat.le_of_dvd hLpos hφL
    omega
  -- Work modulo `Q = q^e`.
  set Q := q ^ e
  have hQpos : 0 < Q := pow_pos hq.pos e
  have hterm : ∀ j : ℕ, ((j ^ L : ℕ) : ZMod Q) = if ¬ q ∣ j then 1 else 0 := by
    intro j
    by_cases hj : q ∣ j
    · simp only [hj, not_true_eq_false, ↓reduceIte]
      rw [ZMod.natCast_eq_zero_iff]
      exact (pow_dvd_pow q heL).trans (pow_dvd_pow_of_dvd hj L)
    · simp only [hj, not_false_eq_true, ↓reduceIte]
      have hco : Nat.Coprime j Q :=
        Nat.Coprime.pow_right e (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hq).mpr hj))
      have ht := Nat.ModEq.pow_totient hco
      obtain ⟨t, ht'⟩ := hφL
      rw [← hphi] at ht'
      have : j ^ L ≡ 1 [MOD Q] := by
        rw [ht', pow_mul]
        simpa using ht.pow t
      rw [(ZMod.natCast_eq_natCast_iff _ _ _).mpr this, Nat.cast_one]
  have hsum : ((∑ j ∈ Finset.Ico 1 k, j ^ (carmichael k / 2) : ℕ) : ZMod Q) =
      ((Finset.Ico 1 k).filter (fun j => ¬ q ∣ j)).card := by
    rw [Finset.natCast_card_filter, Nat.cast_sum]
    exact Finset.sum_congr rfl fun j _ => hterm j
  -- Count the `j ∈ [1, k)` prime to `q`.
  have hfilt : (Finset.Ico 1 k).filter (fun j => ¬ q ∣ j) =
      (Finset.range k).filter (fun j => ¬ q ∣ j) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_range]
    constructor
    · rintro ⟨⟨_, h2⟩, h3⟩; exact ⟨h2, h3⟩
    · rintro ⟨h2, h3⟩
      refine ⟨⟨?_, h2⟩, h3⟩
      rcases Nat.eq_zero_or_pos j with rfl | hj
      · exact absurd (dvd_zero q) h3
      · exact hj
  set K := q ^ (e - 1) * m
  have hkK : k = q * K := by
    rw [← hkm]
    simp only [Q, K]
    rw [← mul_assoc, ← pow_succ']
    congr 2; omega
  have hcount : ((Finset.range k).filter (fun j => ¬ q ∣ j)).card = K * (q - 1) := by
    rw [← Nat.count_eq_card_filter_range, hkK]
    exact count_not_dvd_mul hq.pos K
  have hQdvd : Q ∣ ∑ j ∈ Finset.Ico 1 k, j ^ (carmichael k / 2) :=
    (Dvd.intro m hkm).trans hdiv
  rw [← ZMod.natCast_eq_zero_iff, hsum, hfilt, hcount, ZMod.natCast_eq_zero_iff] at hQdvd
  -- `q^e ∣ q^(e-1) m (q-1)` forces `q ∣ m (q-1)`.
  have hQ : Q = q ^ (e - 1) * q := by
    simp only [Q]; rw [← pow_succ]; congr 1; omega
  rw [hQ, show K * (q - 1) = q ^ (e - 1) * (m * (q - 1)) by simp only [K]; ring] at hQdvd
  have hqd := Nat.dvd_of_mul_dvd_mul_left (pow_pos hq.pos _) hQdvd
  rcases (Nat.Prime.dvd_mul hq).mp hqd with h | h
  · exact hm h
  · have := Nat.le_of_dvd (by omega) h; omega

open Classical in
/-- Primes of one class mod 4: the `n` with no prime factor in that class have density 0. -/
theorem A200982_avoid_density_zero (r : ℕ) (hr : r.Coprime 4) (hr4 : r < 4) :
    Tendsto (fun N : ℕ => (Nat.count (fun n => ∀ p ∈ P4 r, ¬ p ∣ n) N : ℝ) / N) atTop
      (𝓝 0) := by
  refine density_zero_of_sieve (P4 r) (fun p hp => hp.1) ?_ (fun p n => p ∣ n) ?_ ?_
  · have h := not_summable_one_div_prime_mod (q := 4) (a := r) (by norm_num) hr
    refine fun hS => h (hS.congr fun n => ?_)
    exact if_congr (by simp [P4, Nat.mod_eq_of_lt hr4]) rfl rfl
  · intro p hp n
    exact (Nat.dvd_mod_iff (dvd_pow_self p two_ne_zero)).symm
  · intro p hp
    have h2 : Nat.count (fun n => p ∣ n) (p ^ 2) = p := by
      rw [sq]; exact count_dvd_mul hp.1.pos p
    refine le_of_le_of_eq (Nat.sub_le p 1) ?_
    convert h2.symm

open Classical in
/-- The terms of A200982 have natural density 0. -/
theorem A200982_density_zero :
    Tendsto (fun N : ℕ => (Nat.count IsTerm N : ℝ) / N) atTop (𝓝 0) := by
  have h1 := A200982_avoid_density_zero 1 (by norm_num) (by norm_num)
  have h3 := A200982_avoid_density_zero 3 (by norm_num) (by norm_num)
  have hor := density_zero_or h1 h3
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hor
    (fun N => by positivity) (fun N => ?_)
  have hle : Nat.count IsTerm N ≤
      Nat.count (fun n => (∀ p ∈ P4 1, ¬ p ∣ n) ∨ (∀ p ∈ P4 3, ¬ p ∣ n)) N := by
    refine Nat.count_mono_left fun k _ hk => ?_
    by_contra hcon
    push Not at hcon
    obtain ⟨⟨p, hp, hpk⟩, ⟨q, hq, hqk⟩⟩ := hcon
    exact A200982_not_term_of_mixed hk.1 hp.1 hp.2 hq.1 hq.2 hpk hqk hk.2
  have hR : (Nat.count IsTerm N : ℝ) ≤
      (Nat.count (fun n => (∀ p ∈ P4 1, ¬ p ∣ n) ∨ (∀ p ∈ P4 3, ¬ p ∣ n)) N : ℝ) := by
    exact_mod_cast hle
  exact div_le_div_of_nonneg_right hR (Nat.cast_nonneg _)
