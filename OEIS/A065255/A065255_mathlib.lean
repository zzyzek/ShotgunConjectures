import Mathlib
import OpenProblemsLib.PNTApps

/-
OEIS A065255.  b(k) = k-th number n whose last decimal digit equals that of sigma(n),
i.e. sigma(n) ≡ n (mod 10).  Conjecture (B. Cloitre, 2002): b(k)/k → 10.

Checked here: the conjecture.
* `A065255_ten_dvd_sigma`: if a prime p ≡ 9 (mod 10) divides n exactly once, then
  10 ∣ sigma(n).
* `A065255_iff`: under the same hypothesis, sigma(n) ≡ n (mod 10) iff 10 ∣ n.
* `A065255_exceptional_density_zero`: the n with no prime p ≡ 9 (mod 10) dividing them
  exactly once have density 0 (sieve `density_zero_of_sieve` of OpenProblemsLib.PNTApps, fed by
  Dirichlet's divergence of the sum of 1/p over p ≡ 9 mod 10, `not_summable_one_div_prime_mod`).
* `A065255_density`: B = {n ≥ 1 : sigma(n) ≡ n (mod 10)} has density 1/10.
* `A065255_main`: b(k)/k → 10, where b(k) = `Nat.nth B (k - 1)` is the k-th element of B
  (stated as `Nat.nth B k / (k + 1) → 10`, k ≥ 0).
Axioms propext, Classical.choice, Quot.sound. Nothing is outside Lean.
-/

open ArithmeticFunction

theorem A065255_ten_dvd_sigma (n p : ℕ) (hp : p.Prime) (h9 : p % 10 = 9)
    (hdvd : p ∣ n) (hnd : ¬ p ^ 2 ∣ n) : 10 ∣ sigma 1 n := by
  obtain ⟨m, rfl⟩ := hdvd
  have hm : ¬ p ∣ m := by
    intro h
    obtain ⟨c, rfl⟩ := h
    exact hnd ⟨c, by ring⟩
  have hcop : Nat.Coprime p m := (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).mpr hm).symm)
  rw [isMultiplicative_sigma.map_mul_of_coprime hcop]
  have hs : sigma 1 p = p + 1 := by
    have := sigma_one_apply_prime_pow (p := p) (i := 1) hp
    rw [pow_one] at this
    rw [this]
    simp [Finset.sum_range_succ]
    ring
  rw [hs]
  exact Dvd.dvd.mul_right (by omega) _

theorem A065255_iff (n p : ℕ) (hp : p.Prime) (h9 : p % 10 = 9)
    (hdvd : p ∣ n) (hnd : ¬ p ^ 2 ∣ n) : sigma 1 n % 10 = n % 10 ↔ n % 10 = 0 := by
  have h := A065255_ten_dvd_sigma n p hp h9 hdvd hnd
  omega

namespace A065255

open Filter Topology OpenProblemsLib.PNTApps

/-- The primes `p ≡ 9 (mod 10)`. -/
def P9 : Set ℕ := {p | p.Prime ∧ p % 10 = 9}

/-- `p` divides `n` exactly once. -/
def G (p n : ℕ) : Prop := p ∣ n ∧ ¬ p ^ 2 ∣ n

/-- The set B of the entry: `n ≥ 1` with `sigma(n) ≡ n (mod 10)`. -/
def B (n : ℕ) : Prop := 1 ≤ n ∧ ArithmeticFunction.sigma 1 n % 10 = n % 10

instance : DecidablePred B := fun n => by unfold B; infer_instance

end A065255

open A065255 Filter Topology OpenProblemsLib.PNTApps

open Classical in
theorem A065255_exceptional_density_zero :
    Tendsto (fun N : ℕ => (Nat.count (fun n => ∀ p ∈ P9, ¬ G p n) N : ℝ) / N) atTop (𝓝 0) := by
  refine density_zero_of_sieve P9 (fun p hp => hp.1) ?_ G ?_ ?_
  · have h := not_summable_one_div_prime_mod (q := 10) (a := 9) (by norm_num) (by norm_num)
    convert h using 3 with n
    simp [P9]
  · intro p hp n
    have hp2 : p ∣ p ^ 2 := dvd_pow_self p two_ne_zero
    simp only [G, Nat.dvd_mod_iff hp2, Nat.dvd_mod_iff (dvd_refl (p ^ 2))]
  · intro p hp
    have hpos := hp.1.pos
    have h1 := count_le_count_add (p := fun n => p ∣ n) (r := G p) (E := fun n => p ^ 2 ∣ n)
      (fun n hn => by simp [G, hn]) (p ^ 2)
    have h2 : Nat.count (fun n => p ∣ n) (p ^ 2) = p := by
      rw [sq]; exact count_dvd_mul hpos p
    have h3 : Nat.count (fun n => p ^ 2 ∣ n) (p ^ 2) = 1 := by
      have := count_dvd_mul (pow_pos hpos 2) 1
      rwa [mul_one] at this
    rw [h2, h3] at h1
    convert (show p - 1 ≤ Nat.count (G p) (p ^ 2) by omega)

open Classical in
theorem A065255_density :
    Tendsto (fun N : ℕ => (Nat.count B N : ℝ) / N) atTop (𝓝 (1 / 10)) := by
  have h10 := tendsto_count_div_of_periodic (fun n => 10 ∣ n) (M := 10) (by norm_num)
    (fun n => (Nat.dvd_mod_iff dvd_rfl).symm)
  have hc : Nat.count (fun n => 10 ∣ n) 10 = 1 := by decide
  rw [hc] at h10
  push_cast at h10
  refine tendsto_density_of_eq_off (E := fun n => ∀ p ∈ P9, ¬ G p n) (fun n hn => ?_)
    A065255_exceptional_density_zero h10
  push Not at hn
  obtain ⟨p, hp, hpd, hp2⟩ := hn
  have hn0 : n ≠ 0 := by rintro rfl; exact hp2 (dvd_zero _)
  have := A065255_iff n p hp.1 hp.2 hpd hp2
  simp only [B, this, Nat.dvd_iff_mod_eq_zero]
  omega

/-- b(k)/k → 10 for the k-th term b(k) = `Nat.nth B (k - 1)` (k ≥ 1). -/
theorem A065255_main :
    Tendsto (fun k : ℕ => (Nat.nth B k : ℝ) / (k + 1)) atTop (𝓝 10) := by
  have h := tendsto_nth_div_of_density B (by norm_num) A065255_density
  norm_num at h
  have h1 : Tendsto (fun k : ℕ => (k : ℝ) / (k + 1)) atTop (𝓝 1) :=
    tendsto_natCast_div_add_atTop (1 : ℝ)
  have := h.mul h1
  rw [mul_one] at this
  refine this.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with k hk
  have : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  field_simp
