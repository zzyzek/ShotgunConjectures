import Mathlib
import OpenProblemsLib.DworkEuler
import OpenProblemsLib.DworkLocal
import OpenProblemsLib.DworkLocalPoly

/-!
# OEIS A176827: a(n,q) is an integer for every integer q ≥ 1

A176827 (P. D. Hanna): `∑ a(n,q) x^n / q^(n(n-1)/2) = A(x,q)` with
`A(x) = exp (∑_{n ≥ 1} A(x/q^n)^n x^n / n)`.

Definitions.
* `bf q g m = m * [x^m] ∑_{n=1}^{m} A(x/q^n)^n x^n / n` with `A = ∑_{i<m} g i x^i`.
* `A q = recSeq (bf q)`: `A 0 = 1`, `(N+1) A (N+1) = ∑_{j ≤ N} bf (j+1) A (N-j)`.
* `a q n = q^(n choose 2) * A q n` (`n choose 2 = n(n-1)/2`).

Checked: `A176827_int : ∀ q ≥ 1, ∀ n, ∃ z : ℤ, a q n = z`, by primes:
* `p ∣ q` (`A176827_pdvd`): `A_bound : v_p (A q N) ≥ -v_p(q) * (N choose 2)` by induction on the
  recurrence (`n choose 2 ≥ v_p n` and `m (N - m) ≥ v_p N - v_p m` absorb the divisions);
* `p ∤ q` (`A_pint`): induction on `N`; approximate `1/q` by an integer `Q` and `A 0..N-1` by
  integers modulo `p^(v_p(N!) + N)`; the integer model `exp (∑ A'(Q^n x)^n x^n / n)` coefficient
  sequence `rowB ... (Q^n)^(m-n)` is integral at every prime (library `rowB_int`, Euler-product
  lemma), and `expQ_perturb` (library `DworkLocal`) transfers `p`-integrality to `A q N`.
Helpers `Wt_*`, `CP_*`, `PV_pow_sub`, `expQ_eq_of_rec` are in library `DworkLocalPoly`.
Not checked: the reading of the OEIS `exp (...)` as the recurrence.
-/

namespace A176827

open Polynomial OpenProblemsLib.Dwork OpenProblemsLib.DworkEuler OpenProblemsLib.DworkLocal

/-- `m * [x^m] ∑_{n=1}^{m} A(x/q^n)^n x^n / n` with `A = ∑_{i<m} g i x^i`. -/
noncomputable def bf (q : ℕ) (g : ℕ → ℚ) (m : ℕ) : ℚ :=
  (m : ℚ) * ∑ n ∈ Finset.Icc 1 m,
    ((((gpoly g m).comp (C (1 / (q : ℚ) ^ n) * X)) ^ n * X ^ n).coeff m) / (n : ℚ)

/-- Coefficients of `A(x) = exp (∑_{n ≥ 1} A(x/q^n)^n x^n / n)`. -/
noncomputable def A (q : ℕ) : ℕ → ℚ := recSeq (bf q)

/-- `a(n,q) = q^(n(n-1)/2) [x^n] A`. -/
noncomputable def a (q n : ℕ) : ℚ := (q : ℚ) ^ (n.choose 2) * A q n

theorem bf_local (q : ℕ) : Local (bf q) := by
  intro g g' m h
  have : gpoly g m = gpoly g' m :=
    Finset.sum_congr rfl (fun i hi => by rw [h i (Finset.mem_range.mp hi)])
  simp only [bf, this]

theorem bf_eq (q : ℕ) (g : ℕ → ℚ) (m : ℕ) :
    bf q g m = ∑ n ∈ Finset.Icc 1 m,
      (m : ℚ) / n * (1 / (q : ℚ) ^ (n * (m - n))) * ((gpoly g m) ^ n).coeff (m - n) := by
  rw [bf, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [Finset.mem_Icc] at hn
  rw [coeff_mul_X_pow', ← pow_comp, coeff_comp_C_mul_X]
  simp only [hn.2, ↓reduceIte]
  rw [one_div_pow, ← pow_mul]
  ring

/-! ## `n choose 2` -/

theorem T_ge (n : ℕ) : n - 1 ≤ n.choose 2 := by
  induction n with
  | zero => simp
  | succ n ih => rw [choose_two_succ]; omega

section
variable {p : ℕ} [hp : Fact p.Prime]

theorem vp_le (n : ℕ) (hn : 1 ≤ n) : padicValNat p n ≤ n - 1 := by
  have h1 : p ^ padicValNat p n ≤ n := Nat.le_of_dvd (by omega) pow_padicValNat_dvd
  have h2 : padicValNat p n < p ^ padicValNat p n := Nat.lt_pow_self hp.out.one_lt
  omega

theorem key_ineq (v N m n : ℕ) (hv : 1 ≤ v) (hn : 1 ≤ n) (hnm : n ≤ m) (hmN : m ≤ N) :
    (padicValNat p N : ℤ) - ((v * N.choose 2 : ℕ) : ℤ) + ((v * (N - m).choose 2 : ℕ) : ℤ) ≤
      (padicValNat p m : ℤ) - padicValNat p n + -((v * (n * (m - n)) : ℕ) : ℤ) +
        -((v * (m - n).choose 2 : ℕ) : ℤ) := by
  have e1 : N.choose 2 = m.choose 2 + (N - m).choose 2 + m * (N - m) := by
    have := choose_two_add m (N - m); rwa [Nat.add_sub_cancel' hmN] at this
  have e2 : m.choose 2 = n.choose 2 + (m - n).choose 2 + n * (m - n) := by
    have := choose_two_add n (m - n); rwa [Nat.add_sub_cancel' hnm] at this
  have h1 : padicValNat p n ≤ n.choose 2 := (vp_le n hn).trans (T_ge n)
  have h2 : padicValNat p N ≤ padicValNat p m + m * (N - m) := by
    rcases eq_or_lt_of_le hmN with rfl | hlt
    · simp
    · have h3 := vp_le (p := p) N (by omega)
      have h4 : N - 1 ≤ m * (N - m) := by
        obtain ⟨k, hk⟩ : ∃ k, N - m = k + 1 := ⟨N - m - 1, by omega⟩
        obtain ⟨b, hb⟩ : ∃ b, m = b + 1 := ⟨m - 1, by omega⟩
        rw [hk, hb]
        have : N - 1 = b + k + 1 := by omega
        rw [this]; nlinarith
      omega
  rw [e1, e2]
  have h1' : (padicValNat p n : ℤ) ≤ (n.choose 2 : ℕ) := by exact_mod_cast h1
  have h2' : (padicValNat p N : ℤ) ≤ (padicValNat p m : ℤ) + ((m * (N - m) : ℕ) : ℤ) := by
    exact_mod_cast h2
  have hv' : (1 : ℤ) ≤ v := by exact_mod_cast hv
  have hT : (0 : ℤ) ≤ ((n.choose 2 : ℕ) : ℤ) := by positivity
  have hM : (0 : ℤ) ≤ ((m * (N - m) : ℕ) : ℤ) := by positivity
  have k1 := mul_le_mul_of_nonneg_right hv' hT
  have k2 := mul_le_mul_of_nonneg_right hv' hM
  push_cast at h2' hM k2 ⊢
  nlinarith

theorem bf_bound (q : ℕ) (hq : q ≠ 0) (m : ℕ) (g : ℕ → ℚ)
    (hg : ∀ i, i < m → PV p (-((padicValNat p q * i.choose 2 : ℕ) : ℤ)) (g i)) (E : ℤ)
    (hE : ∀ n, 1 ≤ n → n ≤ m → E ≤ (padicValNat p m : ℤ) - padicValNat p n +
      -((padicValNat p q * (n * (m - n)) : ℕ) : ℤ) +
        -((padicValNat p q * (m - n).choose 2 : ℕ) : ℤ)) :
    PV p E (bf q g m) := by
  rw [bf_eq]
  apply PV_sum; intro n hn
  rw [Finset.mem_Icc] at hn
  have h1 := PV_div_nat (PV_nat_self (p := p) m) n (by omega)
  have h2 := PV_inv_qpow (p := p) q hq (n * (m - n))
  have h3 := Wt_pow (Wt_gpoly (p := p) (m := m) hg) n (m - n)
  exact PV_mono (PV_mul (PV_mul h1 h2) h3) (hE n hn.1 hn.2)

theorem A_bound (q : ℕ) (hq : q ≠ 0) (hpq : p ∣ q) :
    ∀ N, PV p (-((padicValNat p q * N.choose 2 : ℕ) : ℤ)) (A q N) := by
  have hv : 1 ≤ padicValNat p q := one_le_padicValNat_of_dvd hq hpq
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    rcases N with _ | N
    · simpa [A, recSeq_zero] using PV_int (p := p) 1
    · have key := recSeq_rec (bf q) (bf_local q) N
      set v := padicValNat p q
      set K0 : ℤ := (padicValNat p (N + 1) : ℤ) - ((v * (N + 1).choose 2 : ℕ) : ℤ)
      have hS : PV p K0 (∑ j ∈ Finset.range (N + 1), bf q (recSeq (bf q)) (j + 1) *
          recSeq (bf q) (N - j)) := by
        apply PV_sum; intro j hj
        rw [Finset.mem_range] at hj
        have hb := bf_bound (p := p) q hq (j + 1) (recSeq (bf q))
          (fun i hi => ih i (by omega)) (K0 + ((v * (N - j).choose 2 : ℕ) : ℤ))
          (fun n h1 h2 => by
            have := key_ineq (p := p) v (N + 1) (j + 1) n hv h1 h2 (by omega)
            rw [show N + 1 - (j + 1) = N - j by omega] at this
            exact this)
        refine PV_mono (PV_mul hb (ih (N - j) (by omega))) ?_
        omega
      have hδ : recSeq (bf q) (N + 1) = (∑ j ∈ Finset.range (N + 1),
          bf q (recSeq (bf q)) (j + 1) * recSeq (bf q) (N - j)) / ((N + 1 : ℕ) : ℚ) := by
        rw [eq_div_iff (by positivity)]; push_cast; rw [mul_comm]; exact key
      show PV p _ (recSeq (bf q) (N + 1))
      rw [hδ]
      have := PV_div_nat hS (N + 1) (by omega)
      convert this using 1; ring

end

/-- At a prime `p ∣ q`, `a(n,q)` is `p`-integral. -/
theorem A176827_pdvd (q n : ℕ) (hq : 1 ≤ q) (p : ℕ) (hp : p.Prime) (hpq : p ∣ q) :
    PV p 0 (a q n) := by
  have := Fact.mk hp
  have h := PV_mul (PV_qpow (p := p) q (n.choose 2)) (A_bound q (by omega) hpq n)
  simpa [a] using h

/-! ## The case `p ∤ q`: approximate `1/q` and `A` by integers, compare with an integer model -/

section
variable {p : ℕ} [hp : Fact p.Prime]

theorem rowB_cast (g' : ℕ → ℤ) (Q : ℤ) (N m : ℕ) (hm : m ≤ N) :
    (rowB ((X * gpoly g' N).map C) (fun _ => 0) (fun m n => (Q ^ n) ^ (m - n)) m : ℚ) =
      ∑ n ∈ Finset.Icc 1 m, (m : ℚ) / n * (Q : ℚ) ^ (n * (m - n)) *
        ((gpoly (fun i => (g' i : ℚ)) m) ^ n).coeff (m - n) := by
  rw [rowB_eq_Icc]
  push_cast
  apply Finset.sum_congr rfl
  intro n hn
  rw [Finset.mem_Icc] at hn
  rw [V_cast_map, coeff_X_mul_gpoly_pow g' N m n hm hn.2, ← pow_mul]
  ring

theorem A_pint (q : ℕ) (hpq : ¬ p ∣ q) : ∀ N, PV p 0 (A q N) := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    set K := padicValNat p N.factorial + N
    have hr : PV p 0 (1 / (q : ℚ)) := by simpa using PV_inv_coprime (p := p) q 1 hpq
    obtain ⟨Q, hQ⟩ := approx hr K
    have hgex : ∀ i, ∃ z : ℤ, i < N → PV p K (A q i - z) := by
      intro i
      by_cases h : i < N
      · obtain ⟨z, hz⟩ := approx (ih i h) K
        exact ⟨z, fun _ => hz⟩
      · exact ⟨0, fun h' => absurd h' h⟩
    choose g' hg' using hgex
    set b : ℕ → ℚ := fun m => bf q (A q) m
    set b' : ℕ → ℤ := rowB ((X * gpoly g' N).map C) (fun _ => 0) (fun m n => (Q ^ n) ^ (m - n))
    have hA : ∀ n, A q n = expQ b n :=
      expQ_eq_of_rec b (A q) (recSeq_zero _) (fun n => recSeq_rec (bf q) (bf_local q) n)
    have hint : ∀ n, n ≤ N → PV p 0 (expQ (fun m => (b' m : ℚ)) n) := by
      intro n _
      obtain ⟨z, hz⟩ := rowB_int ((X * gpoly g' N).map C) (fun _ => 0) ycond_zero
        (fun m n => (Q ^ n) ^ (m - n))
        (fun p hp => W1_pow p hp (fun n => Q ^ n) (LGp_zpow p hp Q) (fun m n => m - n)
          (fun m n => (Nat.mul_sub p m n).symm) (fun k m n hm hn => Nat.dvd_sub hm hn)) n
      rw [expQ_cast, hz]; exact PV_int z
    have hd : ∀ m, 1 ≤ m → m ≤ N →
        PV p (padicValNat p N.factorial) (b m - (b' m : ℚ)) := by
      intro m hm1 hmN
      simp only [b, b']
      rw [bf_eq, rowB_cast g' Q N m hmN, ← Finset.sum_sub_distrib]
      apply PV_sum; intro n hn
      rw [Finset.mem_Icc] at hn
      set c := ((gpoly (A q) m) ^ n).coeff (m - n)
      set c' := ((gpoly (fun i => (g' i : ℚ)) m) ^ n).coeff (m - n)
      set k := n * (m - n)
      have e : (m : ℚ) / n * (1 / (q : ℚ) ^ k) * c - (m : ℚ) / n * (Q : ℚ) ^ k * c' =
          (m : ℚ) / n * ((1 / (q : ℚ)) ^ k * (c - c') + ((1 / (q : ℚ)) ^ k - (Q : ℚ) ^ k) * c') := by
        rw [one_div_pow]; ring
      rw [e]
      have hf : CP p 0 (gpoly (A q) m) := by
        intro i; rw [coeff_gpoly]; split_ifs with hi
        · exact ih i (by omega)
        · exact PV_zero _
      have hf' : CP p 0 (gpoly (fun i => (g' i : ℚ)) m) := by
        intro i; rw [coeff_gpoly]; split_ifs with hi
        · exact PV_int _
        · exact PV_zero _
      have hdf : CP p K (gpoly (A q) m - gpoly (fun i => (g' i : ℚ)) m) := by
        intro i; rw [coeff_sub, coeff_gpoly, coeff_gpoly]; split_ifs with hi
        · exact hg' i (by omega)
        · rw [sub_zero]; exact PV_zero _
      have hcc : PV p K (c - c') := by
        have := CP_pow_sub hf hf' hdf n (m - n)
        rwa [coeff_sub] at this
      have hc' : PV p 0 c' := CP_pow hf' n (m - n)
      have hQ0 : PV p 0 (Q : ℚ) := PV_int Q
      have hqk := PV_pow_sub hr hQ0 hQ k
      have h1 : PV p K ((1 / (q : ℚ)) ^ k * (c - c') + ((1 / (q : ℚ)) ^ k - (Q : ℚ) ^ k) * c') := by
        apply PV_add
        · have := PV_mul (PV_pow0 hr k) hcc; rwa [zero_add] at this
        · have := PV_mul hqk hc'; rwa [add_zero] at this
      have h2 := PV_div_nat (PV_nat_self (p := p) m) n (by omega)
      have h3 := PV_mul h2 h1
      refine PV_mono h3 ?_
      have h4 := vp_le (p := p) n hn.1
      have h5 : (padicValNat p n : ℤ) ≤ N := by exact_mod_cast (show padicValNat p n ≤ N by omega)
      simp only [K, Nat.cast_add]; omega
    rw [hA]
    exact (expQ_perturb b (fun m => (b' m : ℚ)) (padicValNat p N.factorial) N le_rfl
      (fun m _ _ => PV_int _) hint hd N le_rfl).2

end

/-- A176827: `a(n,q)` is an integer for every integer `q ≥ 1` and every `n`. -/
theorem A176827_int (q n : ℕ) (hq : 1 ≤ q) : ∃ z : ℤ, a q n = z := by
  apply int_of_PV
  intro p hp
  have := Fact.mk hp
  by_cases hpq : p ∣ q
  · exact A176827_pdvd q n hq p hp hpq
  · have h := PV_mul (PV_int (p := p) ((q : ℤ) ^ n.choose 2)) (A_pint q hpq n)
    simpa [a] using h

