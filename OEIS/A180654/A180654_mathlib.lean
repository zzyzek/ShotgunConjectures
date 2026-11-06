import Mathlib

/-
OEIS A180654 (P. D. Hanna, 2010): e.g.f. Σ_{n≥0} log(Σ_{k=0..n} C(n,k)^2 x^k)^n/(n! n^n).
Conjecture 1: the coefficients a(N) = N! [x^N] (...) are integers. Conjecture 2: the same with
C(n,k)^p for every p ≥ 1. Conjecture 3: the same with C(n,k)^n.

Definitions.
* `ell P N`: coefficients of x·(log P)' for P = Σ P(k) x^k with P(0) = 1, by the recurrence
  ell N = N P(N) - Σ_{i<N} ell(i) P(N-i) (i.e. x L' · P = x P').
* `logS P = Σ_{N≥1} (ell P N / N) x^N` = log P (the series L with L(0) = 0, x L' P = x P').
* `aSeq e N = N! [x^N] Σ_{n=0..N} logS(P_n)^n / (n! n^n)` with P_n(k) = C(n,k)^(e n); as in the
  entry's PARI program the sum stops at n = N (later terms have x-order > N).

Main theorems.
* `A180654_general e (he : ∀ n, 1 ≤ n → 1 ≤ e n) N : ∃ z : ℤ, aSeq e N = z`.
* `A180654_conj1` (e = 2), `A180654_conj2` (p ≥ 1), `A180654_conj3` (e n = n).

Route: k C(n,k) = n C(n-1,k-1) gives n ∣ k P_n(k), hence n ∣ ell P_n N (`ell_dvd`), so
g = log(P_n)/n has N g_N ∈ ℤ. Divided powers: D_m = g^m/m! has N! [x^N] D_m ∈ ℤ by induction on m,
via θ D_{m+1} = θg · D_m (θ = x d/dx) and (N-1)! [x^N](T E) ∈ ℤ for T with integer coefficients,
T(0) = 0, and E with integer N! [x^N] E (`step`).
Not checked here: that `logS` is the OEIS log (the defining relation L(0) = 0, x L' P = x P').
-/

namespace A180654

open PowerSeries

/-- θ = x d/dx over ℚ -/
noncomputable def theta (f : ℚ⟦X⟧) : ℚ⟦X⟧ := PowerSeries.mk fun n => (n : ℚ) * coeff n f

theorem coeff_theta (f : ℚ⟦X⟧) (n : ℕ) : coeff n (theta f) = n * coeff n f := by
  simp [theta]

theorem theta_mul (f g : ℚ⟦X⟧) : theta (f * g) = theta f * g + f * theta g := by
  ext n
  rw [coeff_theta, map_add, coeff_mul, coeff_mul, coeff_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x hx
  have hx' := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
  rw [coeff_theta, coeff_theta, ← hx']
  push_cast; ring

theorem theta_pow (f : ℚ⟦X⟧) (n : ℕ) :
    theta (f ^ (n + 1)) = C ((n + 1 : ℕ) : ℚ) * f ^ n * theta f := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, theta_mul, ih]
    simp only [map_natCast]
    push_cast; ring

theorem theta_mul_C (f : ℚ⟦X⟧) (c : ℚ) : theta (f * C c) = theta f * C c := by
  ext n
  rw [coeff_theta, coeff_mul_C, coeff_mul_C, coeff_theta]; ring

/-- integer exponential-generating-function coefficients -/
def Hur (f : ℚ⟦X⟧) : Prop := ∀ N, ∃ z : ℤ, (N.factorial : ℚ) * coeff N f = z

theorem step (t : ℕ → ℤ) (ht : t 0 = 0) (E : ℚ⟦X⟧) (hE : Hur E) (N : ℕ) :
    ∃ z : ℤ, ((N - 1).factorial : ℚ) * coeff N (PowerSeries.mk (fun i => (t i : ℚ)) * E) = z := by
  choose e he using hE
  refine ⟨∑ p ∈ Finset.HasAntidiagonal.antidiagonal N, t p.1 * (((N - 1).factorial / p.2.factorial : ℕ) : ℤ) * e p.2, ?_⟩
  rw [coeff_mul, Finset.mul_sum, Int.cast_sum]
  apply Finset.sum_congr rfl
  intro p hp
  have hp' := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
  rw [Int.cast_mul, Int.cast_mul, Int.cast_natCast, coeff_mk, ← he p.2]
  rcases Nat.eq_zero_or_pos p.1 with h0 | h0
  · rw [h0, ht]; simp
  · have hle : p.2 ≤ N - 1 := by omega
    have hd : p.2.factorial ∣ (N - 1).factorial := Nat.factorial_dvd_factorial hle
    have hc : (((N - 1).factorial / p.2.factorial : ℕ) : ℚ) * (p.2.factorial : ℚ)
        = ((N - 1).factorial : ℚ) := by
      rw [← Nat.cast_mul, Nat.div_mul_cancel hd]
    rw [← hc]; ring

/-- divided powers of g with N g_N ∈ ℤ, g_0 = 0 -/
theorem divpow (g : ℚ⟦X⟧) (t : ℕ → ℤ) (ht0 : t 0 = 0)
    (ht : ∀ N : ℕ, (N : ℚ) * coeff N g = t N) (hg0 : coeff 0 g = 0) (m : ℕ) :
    Hur (g ^ m * C (1 / (m.factorial : ℚ))) := by
  have hT : theta g = PowerSeries.mk (fun i => (t i : ℚ)) := by
    ext N; rw [coeff_theta, coeff_mk, ht]
  induction m with
  | zero =>
    intro N
    refine ⟨if N = 0 then 1 else 0, ?_⟩
    rw [pow_zero, one_mul, coeff_C]
    split_ifs with h <;> simp [h]
  | succ m ih =>
    intro N
    rcases Nat.eq_zero_or_pos N with hN | hN
    · subst hN
      refine ⟨0, ?_⟩
      rw [coeff_mul_C, coeff_zero_eq_constantCoeff_apply, map_pow,
        ← coeff_zero_eq_constantCoeff_apply, hg0]
      simp
    · have hth : theta (g ^ (m + 1) * C (1 / ((m + 1).factorial : ℚ)))
          = PowerSeries.mk (fun i => (t i : ℚ)) * (g ^ m * C (1 / (m.factorial : ℚ))) := by
        rw [theta_mul_C, theta_pow, hT]
        have hf : ((m + 1 : ℕ) : ℚ) * (1 / ((m + 1).factorial : ℚ)) = 1 / (m.factorial : ℚ) := by
          rw [Nat.factorial_succ]; push_cast
          field_simp
        calc C ((m + 1 : ℕ) : ℚ) * g ^ m * PowerSeries.mk (fun i => (t i : ℚ))
              * C (1 / ((m + 1).factorial : ℚ))
            = PowerSeries.mk (fun i => (t i : ℚ)) * g ^ m
              * (C ((m + 1 : ℕ) : ℚ) * C (1 / ((m + 1).factorial : ℚ))) := by ring
          _ = _ := by rw [← map_mul, hf]; ring
      obtain ⟨z, hz⟩ := step t ht0 _ ih N
      refine ⟨z, ?_⟩
      rw [← hth, coeff_theta] at hz
      rw [← hz]
      obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
      rw [Nat.factorial_succ, show M + 1 - 1 = M by omega]
      push_cast; ring

/-! ## The logarithm and the sequence -/

def ell (P : ℕ → ℤ) : ℕ → ℤ
  | N => N * P N - ∑ i : Fin N, ell P i * P (N - i)
termination_by N => N
decreasing_by exact i.2

theorem ell_eq (P : ℕ → ℤ) (N : ℕ) : ell P N = N * P N - ∑ i : Fin N, ell P i * P (N - i) := by
  rw [ell]

theorem ell_dvd (P : ℕ → ℤ) (n : ℤ) (h : ∀ k : ℕ, n ∣ (k : ℤ) * P k) (N : ℕ) : n ∣ ell P N := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    rw [ell_eq]
    exact dvd_sub (h N) (Finset.dvd_sum fun i _ => dvd_mul_of_dvd_left (ih i i.2) _)

noncomputable def logS (P : ℕ → ℤ) : ℚ⟦X⟧ :=
  PowerSeries.mk fun N => if N = 0 then 0 else (ell P N : ℚ) / N

def Pn (e : ℕ → ℕ) (n k : ℕ) : ℤ := (n.choose k : ℤ) ^ (e n)

noncomputable def aSeq (e : ℕ → ℕ) (N : ℕ) : ℚ :=
  (N.factorial : ℚ) * coeff N (∑ n ∈ Finset.range (N + 1),
    logS (Pn e n) ^ n * C (1 / ((n.factorial : ℚ) * (n : ℚ) ^ n)))

theorem Pn_dvd (e : ℕ → ℕ) (n : ℕ) (hn : 1 ≤ n) (he : 1 ≤ e n) (k : ℕ) :
    (n : ℤ) ∣ (k : ℤ) * Pn e n k := by
  unfold Pn
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk; simp
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have h1 : ((k' + 1 : ℕ) : ℤ) * ((n' + 1).choose (k' + 1) : ℤ)
      = ((n' + 1 : ℕ) : ℤ) * (n'.choose k' : ℤ) := by
    have := Nat.add_one_mul_choose_eq n' k'
    have h2 : (k' + 1) * (n' + 1).choose (k' + 1) = (n' + 1) * n'.choose k' := by
      rw [this]; ring
    exact_mod_cast h2
  obtain ⟨q, hq⟩ : ∃ q, e (n' + 1) = q + 1 := ⟨e (n' + 1) - 1, by omega⟩
  rw [hq, pow_succ]
  have h3 : ((k' + 1 : ℕ) : ℤ) * (((n' + 1).choose (k' + 1) : ℤ) ^ q * ((n' + 1).choose (k' + 1) : ℤ))
      = ((n' + 1 : ℕ) : ℤ) * ((n'.choose k' : ℤ) * ((n' + 1).choose (k' + 1) : ℤ) ^ q) := by
    linear_combination (((n' + 1).choose (k' + 1) : ℤ) ^ q) * h1
  push_cast at h3 ⊢
  rw [h3]
  exact dvd_mul_right _ _

theorem term_hur (e : ℕ → ℕ) (he : ∀ n, 1 ≤ n → 1 ≤ e n) (n : ℕ) :
    Hur (logS (Pn e n) ^ n * C (1 / ((n.factorial : ℚ) * (n : ℚ) ^ n))) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    intro N
    refine ⟨if N = 0 then 1 else 0, ?_⟩
    rw [pow_zero, one_mul, coeff_C]
    split_ifs with h <;> simp [h]
  have hd := ell_dvd (Pn e n) n (Pn_dvd e n hn (he n hn))
  choose t ht using hd
  set g := logS (Pn e n) * C (1 / (n : ℚ)) with hgdef
  have hn0 : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  have heq : logS (Pn e n) ^ n * C (1 / ((n.factorial : ℚ) * (n : ℚ) ^ n))
      = g ^ n * C (1 / (n.factorial : ℚ)) := by
    rw [hgdef, mul_pow, ← map_pow, mul_assoc, ← map_mul]
    congr 2
    field_simp
    rw [← mul_pow, mul_one_div_cancel hn0, one_pow]
  rw [heq]
  have ht0 : t 0 = 0 := by
    have := ht 0
    rw [ell_eq] at this
    simp at this
    rcases this with h | h
    · exact absurd h (by exact_mod_cast hn.ne')
    · exact h
  apply divpow g t ht0
  · intro N
    rw [hgdef, coeff_mul_C, logS, coeff_mk]
    split_ifs with hN
    · subst hN; simp [ht0]
    · rw [ht N]
      have hN' : (N : ℚ) ≠ 0 := by exact_mod_cast hN
      push_cast
      field_simp
  · rw [hgdef, coeff_mul_C, logS, coeff_mk]; simp

theorem A180654_general (e : ℕ → ℕ) (he : ∀ n, 1 ≤ n → 1 ≤ e n) (N : ℕ) :
    ∃ z : ℤ, aSeq e N = z := by
  have h := fun n => term_hur e he n N
  choose z hz using h
  refine ⟨∑ n ∈ Finset.range (N + 1), z n, ?_⟩
  unfold aSeq
  rw [map_sum, Finset.mul_sum]
  push_cast
  exact Finset.sum_congr rfl fun n _ => hz n

/-- Conjecture 1 (the sequence A180654 itself, C(n,k)^2). -/
theorem A180654_conj1 (N : ℕ) : ∃ z : ℤ, aSeq (fun _ => 2) N = z :=
  A180654_general _ (fun _ _ => by norm_num) N

/-- Conjecture 2: C(n,k)^p for every p ≥ 1. -/
theorem A180654_conj2 (p : ℕ) (hp : 1 ≤ p) (N : ℕ) : ∃ z : ℤ, aSeq (fun _ => p) N = z :=
  A180654_general _ (fun _ _ => hp) N

/-- Conjecture 3: C(n,k)^n. -/
theorem A180654_conj3 (N : ℕ) : ∃ z : ℤ, aSeq (fun n => n) N = z :=
  A180654_general _ (fun _ h => h) N
