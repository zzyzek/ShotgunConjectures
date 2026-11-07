import Mathlib
import OpenProblemsLib.DworkEuler
import OpenProblemsLib.DworkLocal

/-!
# p-adic bounds for rational polynomials and recurrences (companion to `DworkLocal`)

Declarations live in the namespace `OpenProblemsLib.DworkLocal`, beside `PV`.
`p` is a prime throughout.

* `choose_two_succ`, `choose_two_add` : `(n+1).choose 2 = n.choose 2 + n` and
  `(i+j).choose 2 = i.choose 2 + j.choose 2 + i j`.
* `Wt p v f` : `v_p ([x^i] f) ≥ -v (i choose 2)` for every `i`. Closed under products
  (`Wt_mul`, `Wt_one`, `Wt_pow`); `Wt_gpoly` for truncations `gpoly g m` of a sequence obeying
  the bound below `m`.
* `PV_nat_self` : `v_p m ≥ v_p m`; `PV_qpow`, `PV_inv_qpow` : `v_p (q^k) = k v_p q` as
  `PV` bounds in both directions.
* `CP p k f` : coefficientwise `p^k ∣ f`. `CP_mul`, `CP_one`, `CP_pow`, `CP_sum`, and
  `CP_pow_sub` : `f ≡ f' (mod p^K)` with `p`-integral `f, f'` gives `f^n ≡ f'^n (mod p^K)`.
* `PV_pow0`, `PV_pow_sub` : the same two facts for rationals.
* `expQ_eq_of_rec` : a sequence with `A 0 = 1` and `(n+1) A (n+1) = ∑_{j ≤ n} b (j+1) A (n-j)`
  is `expQ b`.

Used by OEIS A176827.
-/

namespace OpenProblemsLib.DworkLocal

open Polynomial OpenProblemsLib.Dwork OpenProblemsLib.DworkEuler

/-! ## `n choose 2` -/

theorem choose_two_succ (n : ℕ) : (n + 1).choose 2 = n.choose 2 + n := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, Nat.choose_succ_succ, Nat.choose_one_right]; ring

theorem choose_two_add (i j : ℕ) : (i + j).choose 2 = i.choose 2 + j.choose 2 + i * j := by
  induction j with
  | zero => simp
  | succ j ih => rw [← add_assoc, choose_two_succ, ih, choose_two_succ]; ring

section
variable {p : ℕ} [hp : Fact p.Prime]

/-! ## Weighted coefficient bounds -/

/-- `v_p ([x^i] f) ≥ -v (i choose 2)` for every `i`. -/
def Wt (p v : ℕ) (f : ℚ[X]) : Prop := ∀ i, PV p (-((v * i.choose 2 : ℕ) : ℤ)) (f.coeff i)

theorem Wt_mul {v : ℕ} {f g : ℚ[X]} (hf : Wt p v f) (hg : Wt p v g) : Wt p v (f * g) := by
  intro k
  rw [coeff_mul]
  apply PV_sum; intro x hx
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
  refine PV_mono (PV_mul (hf x.1) (hg x.2)) ?_
  rw [← hx, choose_two_add]; push_cast
  have : (0 : ℤ) ≤ (v : ℤ) * ((x.1 : ℤ) * x.2) := by positivity
  nlinarith

theorem Wt_one (v : ℕ) : Wt p v 1 := by
  intro i
  rw [coeff_one]
  split_ifs with h
  · subst h; simpa using PV_int (p := p) 1
  · exact PV_zero _

theorem Wt_pow {v : ℕ} {f : ℚ[X]} (hf : Wt p v f) (n : ℕ) : Wt p v (f ^ n) := by
  induction n with
  | zero => rw [pow_zero]; exact Wt_one v
  | succ n ih => rw [pow_succ]; exact Wt_mul ih hf

theorem Wt_gpoly {v m : ℕ} {g : ℕ → ℚ}
    (h : ∀ i, i < m → PV p (-((v * i.choose 2 : ℕ) : ℤ)) (g i)) :
    Wt p v (gpoly g m) := by
  intro i
  rw [coeff_gpoly]
  split_ifs with hi
  · exact h i hi
  · exact PV_zero _

/-! ## Powers of a natural number -/

theorem PV_inv_qpow (q : ℕ) (hq : q ≠ 0) (k : ℕ) :
    PV p (-((padicValNat p q * k : ℕ) : ℤ)) (1 / (q : ℚ) ^ k) := by
  have hq' : (q : ℚ) ≠ 0 := by exact_mod_cast hq
  have hv : padicValRat p ((q : ℚ) ^ k) = ((padicValNat p q * k : ℕ) : ℤ) := by
    rw [padicValRat.pow, ← padicValRat_of_nat]; push_cast; ring
  unfold PV
  rw [padicNorm.div, padicNorm.one, padicNorm.eq_zpow_of_nonzero (pow_ne_zero _ hq'), hv, one_div,
    ← zpow_neg]

theorem PV_qpow (q k : ℕ) : PV p ((padicValNat p q * k : ℕ) : ℤ) ((q : ℚ) ^ k) := by
  have h : ((p : ℤ) ^ padicValNat p q) ∣ (q : ℤ) := by exact_mod_cast pow_padicValNat_dvd
  have h2 : ((p : ℤ) ^ (padicValNat p q * k)) ∣ (q : ℤ) ^ k := by
    rw [pow_mul]; exact pow_dvd_pow_of_dvd h k
  simpa using PV_dvd (p := p) _ _ h2

theorem PV_nat_self (m : ℕ) : PV p (padicValNat p m) (m : ℚ) := by
  have h : ((p : ℤ) ^ padicValNat p m) ∣ (m : ℤ) := by exact_mod_cast pow_padicValNat_dvd
  simpa using PV_dvd (p := p) _ _ h

/-! ## Coefficientwise divisibility and differences of powers -/

/-- Coefficientwise `p^k ∣ f`. -/
def CP (p : ℕ) (k : ℤ) (f : ℚ[X]) : Prop := ∀ i, PV p k (f.coeff i)

theorem CP_mul {k l : ℤ} {f g : ℚ[X]} (hf : CP p k f) (hg : CP p l g) : CP p (k + l) (f * g) := by
  intro i
  rw [coeff_mul]
  exact PV_sum _ _ (fun x _ => PV_mul (hf x.1) (hg x.2))

theorem CP_one : CP p 0 (1 : ℚ[X]) := by
  intro i
  rw [coeff_one]
  split_ifs
  · simpa using PV_int (p := p) 1
  · exact PV_zero _

theorem CP_pow {f : ℚ[X]} (hf : CP p 0 f) (n : ℕ) : CP p 0 (f ^ n) := by
  induction n with
  | zero => rw [pow_zero]; exact CP_one
  | succ n ih => rw [pow_succ]; have := CP_mul ih hf; rwa [zero_add] at this

theorem CP_sum {ι : Type*} (s : Finset ι) (f : ι → ℚ[X]) {k : ℤ} (h : ∀ i ∈ s, CP p k (f i)) :
    CP p k (∑ i ∈ s, f i) := by
  intro j
  rw [finsetSum_coeff]
  exact PV_sum _ _ (fun i hi => h i hi j)

/-- `f ≡ f' (mod p^K)` with `p`-integral `f, f'` gives `f^n ≡ f'^n (mod p^K)`. -/
theorem CP_pow_sub {K : ℤ} {f f' : ℚ[X]} (hf : CP p 0 f) (hf' : CP p 0 f') (hd : CP p K (f - f'))
    (n : ℕ) : CP p K (f ^ n - f' ^ n) := by
  rw [← geom_sum₂_mul]
  have h := CP_mul (CP_sum (Finset.range n) _ (fun i _ => by
    have := CP_mul (CP_pow hf i) (CP_pow hf' (n - 1 - i)); rwa [zero_add] at this)) hd
  rwa [zero_add] at h

theorem PV_pow0 {x : ℚ} (hx : PV p 0 x) (n : ℕ) : PV p 0 (x ^ n) := by
  induction n with
  | zero => simpa using PV_int (p := p) 1
  | succ n ih => rw [pow_succ]; have := PV_mul ih hx; rwa [zero_add] at this

/-- `x ≡ y (mod p^K)` with `p`-integral `x, y` gives `x^n ≡ y^n (mod p^K)`. -/
theorem PV_pow_sub {K : ℤ} {x y : ℚ} (hx : PV p 0 x) (hy : PV p 0 y) (hd : PV p K (x - y))
    (n : ℕ) : PV p K (x ^ n - y ^ n) := by
  rw [← geom_sum₂_mul]
  have h := PV_mul (PV_sum (Finset.range n) _ (fun i _ => by
    have := PV_mul (PV_pow0 hx i) (PV_pow0 hy (n - 1 - i)); rwa [zero_add] at this)) hd
  rwa [zero_add] at h

end

/-- A sequence with `A 0 = 1` and `(n+1) A (n+1) = ∑_{j ≤ n} b (j+1) A (n-j)` is `expQ b`. -/
theorem expQ_eq_of_rec (b : ℕ → ℚ) (A : ℕ → ℚ) (h0 : A 0 = 1)
    (h : ∀ n : ℕ, ((n : ℚ) + 1) * A (n + 1) = ∑ j ∈ Finset.range (n + 1), b (j + 1) * A (n - j)) :
    ∀ n, A n = expQ b n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | n
    · rw [h0, expQ_zero]
    · have e1 := h n
      have e2 := expQ_succ b n
      have hs : ∑ j ∈ Finset.range (n + 1), b (j + 1) * A (n - j) =
          ∑ j ∈ Finset.range (n + 1), b (j + 1) * expQ b (n - j) :=
        Finset.sum_congr rfl (fun j hj => by
          rw [Finset.mem_range] at hj
          rw [ih (n - j) (by omega)])
      have hne : ((n : ℚ) + 1) ≠ 0 := by positivity
      exact mul_left_cancel₀ hne (e1.trans (hs.trans e2.symm))

end OpenProblemsLib.DworkLocal
