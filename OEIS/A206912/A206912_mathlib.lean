/-
OEIS A206912 (offset 1): position of log(n+1) when the partial sums
H_k = 1 + 1/2 + ... + 1/k (k ≥ 1) of the harmonic series are jointly ranked
with the set {log(j+1) : j ≥ 1}.  Conjecture (entry text, via A206911):
the difference sequence of A206912 consists of 1s and 2s.

Definition.  Below log(n+1) lie the n - 1 values log(2), ..., log(n) and the
H_k with H_k < log(n+1), so its position is
  `A206912 n = n + #{k ≥ 1 : H_k < log(n+1)}`
(a `Set.ncard`; the set is finite, see `ncard_eq`).  A tie H_k = log(n+1)
would make the ranking ambiguous; the definition counts H_k strictly below.
Ties do not occur (log(n+1) is irrational), but that fact is not used and
not checked here: the theorem holds for the stated definition either way.

Main theorems.
* `two_consecutive_not_between`: for m ≥ 1 it is impossible that
  log m ≤ H_k and H_{k+1} < log(m+1).
* `A206912_diff`: A206912 (n+1) = A206912 n + 1 ∨ A206912 (n+1) = A206912 n + 2,
  for every n (the conjecture).

Proof.  If log m ≤ H_k and H_{k+1} < log(m+1) then
1/(k+1) < log(m+1) - log m = log(1 + 1/m) ≤ 1/m, so m ≤ k, and then
log(m+1) ≤ log(k+1) ≤ H_k ≤ H_{k+1} < log(m+1).  Hence at most one H_k lies
in [log(n+1), log(n+2)), and A206912(n+1) - A206912(n) = 1 + (that count).

Not checked in this file: that `A206912 n` reproduces the OEIS data terms
(certificate/check.py compares numerically).
-/
import Mathlib

open Finset

/-- The harmonic numbers are monotone. -/
theorem harmonic_monotone : Monotone harmonic := by
  refine monotone_nat_of_le_succ fun n => ?_
  rw [harmonic_succ]
  have : (0 : ℚ) ≤ (↑(n + 1))⁻¹ := by positivity
  linarith

/-- Two consecutive harmonic numbers never both lie in [log m, log(m+1)). -/
theorem two_consecutive_not_between (m k : ℕ) (hm : 1 ≤ m)
    (h1 : Real.log (m : ℝ) ≤ harmonic k)
    (h2 : (harmonic (k + 1) : ℝ) < Real.log ((m : ℝ) + 1)) : False := by
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by linarith
  have hsucc : (harmonic (k + 1) : ℝ) = harmonic k + 1 / ((k : ℝ) + 1) := by
    rw [harmonic_succ]
    push_cast
    ring
  have hlog : Real.log ((m : ℝ) + 1) - Real.log m ≤ 1 / m := by
    rw [← Real.log_div (by positivity) hm0.ne']
    have h := Real.log_le_sub_one_of_pos (x := ((m : ℝ) + 1) / m) (by positivity)
    have e : ((m : ℝ) + 1) / m - 1 = 1 / m := by
      rw [add_div, div_self hm0.ne']
      ring
    linarith
  have hlt : 1 / ((k : ℝ) + 1) < 1 / m := by linarith
  have hmk : (m : ℝ) < k + 1 := by
    rwa [one_div_lt_one_div (by positivity) hm0] at hlt
  have hmkN : m ≤ k := by
    have : m < k + 1 := by exact_mod_cast hmk
    omega
  have hmkR : (m : ℝ) ≤ k := by exact_mod_cast hmkN
  have hlk : Real.log ((m : ℝ) + 1) ≤ Real.log ((k : ℝ) + 1) :=
    Real.log_le_log (by positivity) (by linarith)
  have hH := log_add_one_le_harmonic k
  push_cast at hH
  have : (0 : ℝ) ≤ 1 / ((k : ℝ) + 1) := by positivity
  linarith

/-- Position of log(n+1) among {H_k : k ≥ 1} ∪ {log(j+1) : j ≥ 1}. -/
noncomputable def A206912 (n : ℕ) : ℕ :=
  n + Set.ncard {k : ℕ | 1 ≤ k ∧ (harmonic k : ℝ) < Real.log ((n : ℝ) + 1)}

/-- The indices k ≥ 1 with H_k < log(n+1), as a finset (all are < n). -/
noncomputable def below (n : ℕ) : Finset ℕ :=
  (Finset.range (n + 1)).filter
    (fun k => 1 ≤ k ∧ (harmonic k : ℝ) < Real.log ((n : ℝ) + 1))

/-- H_k < log(n+1) forces k < n, since H_k ≥ log(k+1). -/
theorem lt_of_harmonic_lt {n k : ℕ}
    (h : (harmonic k : ℝ) < Real.log ((n : ℝ) + 1)) : k < n := by
  have hH := log_add_one_le_harmonic k
  push_cast at hH
  have h' : Real.log ((k : ℝ) + 1) < Real.log ((n : ℝ) + 1) := lt_of_le_of_lt hH h
  rw [Real.log_lt_log_iff (by positivity) (by positivity)] at h'
  exact_mod_cast (by linarith : (k : ℝ) < n)

theorem ncard_eq (n : ℕ) :
    Set.ncard {k : ℕ | 1 ≤ k ∧ (harmonic k : ℝ) < Real.log ((n : ℝ) + 1)} =
      (below n).card := by
  rw [← Set.ncard_coe_finset]
  congr 1
  ext k
  simp only [below, Set.mem_ofPred_eq, Finset.coe_filter, Finset.mem_range]
  constructor
  · intro h
    exact ⟨by have := lt_of_harmonic_lt h.2; omega, h⟩
  · intro h
    exact h.2

theorem A206912_eq (n : ℕ) : A206912 n = n + (below n).card := by
  rw [A206912, ncard_eq]

theorem below_subset (n : ℕ) : below n ⊆ below (n + 1) := by
  intro k hk
  simp only [below, Finset.mem_filter, Finset.mem_range] at hk ⊢
  have hle : Real.log ((n : ℝ) + 1) ≤ Real.log (((n + 1 : ℕ) : ℝ) + 1) :=
    Real.log_le_log (by positivity) (by push_cast; linarith)
  exact ⟨by omega, hk.2.1, lt_of_lt_of_le hk.2.2 hle⟩

/-- At most one new index enters when n increases by one. -/
theorem card_new_le_one (n : ℕ) : (below (n + 1) \ below n).card ≤ 1 := by
  have mem : ∀ k ∈ below (n + 1) \ below n,
      Real.log (((n + 1 : ℕ) : ℝ)) ≤ harmonic k ∧
        (harmonic k : ℝ) < Real.log (((n + 1 : ℕ) : ℝ) + 1) := by
    intro k hk
    simp only [below, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_range] at hk
    obtain ⟨⟨_, h1, h2⟩, h3⟩ := hk
    have hkn : k < n + 1 := lt_of_harmonic_lt h2
    refine ⟨?_, h2⟩
    by_contra hc
    replace hc := not_le.mp hc
    push_cast at hc
    exact h3 ⟨by omega, h1, hc⟩
  rw [Finset.card_le_one]
  intro a ha b hb
  have hA := mem a ha
  have hB := mem b hb
  have key : ∀ x y : ℕ, x < y →
      Real.log (((n + 1 : ℕ) : ℝ)) ≤ harmonic x →
      (harmonic y : ℝ) < Real.log (((n + 1 : ℕ) : ℝ) + 1) → False := by
    intro x y hxy hx hy
    have hmono : (harmonic (x + 1) : ℝ) ≤ harmonic y := by
      exact_mod_cast harmonic_monotone (by omega : x + 1 ≤ y)
    exact two_consecutive_not_between (n + 1) x (by omega) hx (by linarith)
  rcases lt_trichotomy a b with h | h | h
  · exact (key a b h hA.1 hB.2).elim
  · exact h
  · exact (key b a h hB.1 hA.2).elim

/-- The conjecture: consecutive differences of A206912 are 1 or 2. -/
theorem A206912_diff (n : ℕ) :
    A206912 (n + 1) = A206912 n + 1 ∨ A206912 (n + 1) = A206912 n + 2 := by
  rw [A206912_eq, A206912_eq]
  have h := Finset.card_sdiff_add_card_eq_card (below_subset n)
  have h1 := card_new_le_one n
  omega
