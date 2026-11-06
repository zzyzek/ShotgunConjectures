/-
OEIS A103990 / A103991: reduced numerators / denominators of sqrt(pi) I(n,0),
I(n,x) the hypercube line-picking integrand (Trott). Conjecture (Gerald
McGarvey, 2009): a(n)/b(n) = (2/3)(n^3 - n^2 + 2n + 1)/(2n + 1).

Reading (README): I(n,x) is the canonical form of
  (1/sqrt(pi)) (1 - d(u)^n)/u^2,   d = (e^{-u^2} - 1 + sqrt(pi) u erf u)/u^2,
modulo integration by parts, in the basis e^{-k u^2} erf(u)^l / u^(l mod 2),
k >= 1 (this reproduces MathWorld's I_1..I_4 and the 20 data terms).
Formal model: t = u^2, X = e^{-u^2}, W = sqrt(pi) erf(u)/u; monomials
t^j X^k W^l are `Mon = ℤ × ℕ × ℕ`; d = W - (1 - X)/t and sqrt(pi) times the
integrand is `Fn n` = (1 - d^n)/t; D(u t^j X^k W^l) is `rel j k l`, allowed
unless k = 0 and l = 2j + 1 (`Rels`); the basis element e^{-k u^2} erf^l /
u^(l mod 2) is t^(l/2) X^k W^l, with value `anc l` at u = 0 (1, 2, 0, ...).

Main theorems.
* `A103990_canonical`: for n ≥ 1, every combination Σ c_p (basis) with
  `Fn n` - Σ c_p (basis) in the span of `Rels` has value at 0
  Σ c_p anc = (2/3)(n^3 - n^2 + 2n + 1)/(2n + 1).
* `A103990_main`: S n = (2/3)(n^3 - n^2 + 2n + 1)/(2n + 1), S n = V(Fn n).

Route.
* `V`: the functional on all monomials, solved from the basis values upwards
  and downwards in j; `V_rel`, `G_rel`, `VL_rel`: it kills every allowed
  relation; `V_anchor`: it equals `anc` on the basis.
* `Vn_eq`: below the anchors V is the recursion `Vn`; `VL_Fn`: V(Fn n) = S n.
* `S_eq`, `T_zero`: Vn τ · l is a polynomial of degree ≤ τ in k, so only two
  top coefficients a, q survive the alternating sums; `a_*`, `q_*`.
* `a_eq`, `q_eq`: closed forms through I α β = ∫_0^1 ρ^(α+β) (ρ-2)^α dρ
  (`ι` = ∫_0^1 on ℚ[X], `ι_deriv`, relations `I0`, `I1`, `Jrel`, `Krel`).
* `diag_qE`: the diagonal sum, by binomial moments `B0`-`B2` under ι.

Not checked here: the reading (that Trott's integrand is such a canonical
combination: the dictionary between the functions and the formal monomials,
and that the published reduction terminates in the basis; certificate/
check_trott.py reproduces I_1..I_4 and the data).
-/
import Mathlib

namespace A103990

open Finset Function fwdDiff

/-- cc τ = (-2)^τ / (2τ-1)!!: the value of t^-τ X^k is cc τ * k^τ. -/
def cc : ℕ → ℚ
  | 0 => 1
  | τ + 1 => -2 * cc τ / (2 * τ + 1)

/-- Vn τ k l = V(t^-τ X^k W^l). -/
def Vn : ℕ → ℕ → ℕ → ℚ
  | τ, k, 0 => cc τ * (k : ℚ) ^ τ
  | 0, _, l + 1 => 2 ^ (l + 1) * ((l : ℚ) + 1)
  | τ + 1, k, l + 1 =>
      (2 * (k : ℚ) * Vn τ k (l + 1) - 2 * ((l : ℚ) + 1) * Vn (τ + 1) (k + 1) l) /
        (1 - 2 * ((τ : ℚ) + 1) - ((l : ℚ) + 1))
termination_by τ _ l => τ + l

/-- √π I(n,0) under the reading: V applied to the expansion of (1 - d^n)/t. -/
def S (n : ℕ) : ℚ :=
  -∑ i ∈ range (n + 1), ∑ m ∈ range (i + 1),
    (n.choose i : ℚ) * (i.choose m) * (-1) ^ (i + m) * Vn (i + 1) m (n - i)

lemma Vn_l0 (τ k : ℕ) : Vn τ k 0 = cc τ * (k : ℚ) ^ τ := by
  rw [Vn]

lemma Vn_t0 (k l : ℕ) : Vn 0 k (l + 1) = 2 ^ (l + 1) * ((l : ℚ) + 1) := by
  rw [Vn]

lemma Vn_succ (τ k l : ℕ) : Vn (τ + 1) k (l + 1) =
    (2 * (k : ℚ) * Vn τ k (l + 1) - 2 * ((l : ℚ) + 1) * Vn (τ + 1) (k + 1) l) /
      (1 - 2 * ((τ : ℚ) + 1) - ((l : ℚ) + 1)) := by
  rw [Vn]

/-! ### Forward differences on ℕ → ℚ -/

lemma fd_succ (F : ℕ → ℚ) (i y : ℕ) :
    (fwdDiff (1 : ℕ))^[i + 1] F y = (fwdDiff (1 : ℕ))^[i] F (y + 1) - (fwdDiff (1 : ℕ))^[i] F y := by
  rw [iterate_succ_apply']
  rfl

lemma fd_lin (f g : ℕ → ℚ) (a b : ℚ) (i y : ℕ) :
    (fwdDiff (1 : ℕ))^[i] (fun k => a * f k + b * g k) y = a * (fwdDiff (1 : ℕ))^[i] f y + b * (fwdDiff (1 : ℕ))^[i] g y := by
  induction i generalizing y with
  | zero => rfl
  | succ i ih =>
    rw [fd_succ, fd_succ f, fd_succ g, ih, ih]
    ring

lemma fd_const (c : ℚ) (i y : ℕ) : (fwdDiff (1 : ℕ))^[i + 1] (fun _ : ℕ => c) y = 0 := by
  induction i generalizing y with
  | zero => simp [fwdDiff]
  | succ i ih => rw [fd_succ, ih, ih, sub_self]

lemma fd_shift (g : ℕ → ℚ) (i y : ℕ) :
    (fwdDiff (1 : ℕ))^[i] (fun k => g (k + 1)) y = (fwdDiff (1 : ℕ))^[i] g (y + 1) :=
  fwdDiff_iter_comp_add 1 g 1 i y

/-- Product rule for k * g k. -/
lemma fd_mul (g : ℕ → ℚ) (i y : ℕ) :
    (fwdDiff (1 : ℕ))^[i + 1] (fun k => (k : ℚ) * g k) y =
      (y : ℚ) * (fwdDiff (1 : ℕ))^[i + 1] g y + ((i : ℚ) + 1) * (fwdDiff (1 : ℕ))^[i] g (y + 1) := by
  induction i generalizing y with
  | zero =>
    simp only [zero_add, iterate_one, iterate_zero, id_eq]
    simp only [fwdDiff]
    push_cast
    ring
  | succ i ih =>
    rw [fd_succ (fun k => (k : ℚ) * g k), ih, ih, fd_succ g (i + 1) y, fd_succ g i (y + 1)]
    push_cast
    ring

lemma fd_zero_mul (g : ℕ → ℚ) (i : ℕ) :
    (fwdDiff (1 : ℕ))^[i + 1] (fun k => (k : ℚ) * g k) 0 =
      ((i : ℚ) + 1) * ((fwdDiff (1 : ℕ))^[i] g 0 + (fwdDiff (1 : ℕ))^[i + 1] g 0) := by
  rw [fd_mul, fd_succ g i 0]
  push_cast
  ring

/-! ### Powers -/

/-- pw τ i = Δ^i (k ↦ k^τ) at 0. -/
def pw (τ i : ℕ) : ℚ := (fwdDiff (1 : ℕ))^[i] (fun k : ℕ => (k : ℚ) ^ τ) 0

lemma pw_succ (τ i : ℕ) : pw (τ + 1) (i + 1) = ((i : ℚ) + 1) * (pw τ i + pw τ (i + 1)) := by
  unfold pw
  rw [show (fun k : ℕ => (k : ℚ) ^ (τ + 1)) = fun k : ℕ => (k : ℚ) * (k : ℚ) ^ τ by
    funext k; ring]
  exact fd_zero_mul _ i

lemma pw_zero_succ (i : ℕ) : pw 0 (i + 1) = 0 := by
  unfold pw
  simp only [pow_zero]
  exact fd_const 1 i 0

lemma pw_zero_left (τ : ℕ) : pw (τ + 1) 0 = 0 := by
  simp [pw]

lemma pw_big (τ i : ℕ) (h : τ < i) : pw τ i = 0 := by
  induction τ generalizing i with
  | zero =>
    obtain ⟨i, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    exact pw_zero_succ i
  | succ τ ih =>
    obtain ⟨i, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    rw [pw_succ, ih i (by omega), ih (i + 1) (by omega)]
    ring

lemma pw_diag (τ : ℕ) : pw τ τ = (τ.factorial : ℚ) := by
  induction τ with
  | zero => simp [pw]
  | succ τ ih =>
    rw [pw_succ, ih, pw_big τ (τ + 1) (by omega), Nat.factorial_succ]
    push_cast
    ring

lemma pw_sub (τ : ℕ) : pw (τ + 1) τ = ((τ + 1).factorial : ℚ) * τ / 2 := by
  induction τ with
  | zero => simp [pw]
  | succ τ ih =>
    rw [pw_succ, ih, pw_diag, Nat.factorial_succ (τ + 1)]
    push_cast
    ring

/-! ### Differences of Vn -/

/-- T τ l i = Δ^i_k Vn τ k l at k = 0. -/
def T (τ l i : ℕ) : ℚ := (fwdDiff (1 : ℕ))^[i] (fun k => Vn τ k l) 0

lemma T_l0 (τ i : ℕ) : T τ 0 i = cc τ * pw τ i := by
  unfold T pw
  simp only [Vn_l0]
  have := fd_lin (fun k : ℕ => (k : ℚ) ^ τ) (fun _ => 0) (cc τ) 0 i 0
  simpa using this

lemma T_t0 (l i : ℕ) : T 0 (l + 1) (i + 1) = 0 := by
  unfold T
  simp only [Vn_t0]
  exact fd_const _ i 0

lemma T_t0_zero (l : ℕ) : T 0 (l + 1) 0 = 2 ^ (l + 1) * ((l : ℚ) + 1) := by
  simp [T, Vn_t0]

/-- The denominator of the recursion. -/
def den (τ l : ℕ) : ℚ := 1 - 2 * ((τ : ℚ) + 1) - ((l : ℚ) + 1)

lemma den_ne (τ l : ℕ) : den τ l ≠ 0 := by
  unfold den
  have : (0 : ℚ) ≤ τ := by positivity
  have : (0 : ℚ) ≤ l := by positivity
  linarith

lemma T_succ (τ l i : ℕ) : T (τ + 1) (l + 1) i =
    (2 * (fwdDiff (1 : ℕ))^[i] (fun k => (k : ℚ) * Vn τ k (l + 1)) 0 -
      2 * ((l : ℚ) + 1) * (T (τ + 1) l i + T (τ + 1) l (i + 1))) / den τ l := by
  unfold T
  have hf : (fun k : ℕ => Vn (τ + 1) k (l + 1)) = fun k : ℕ =>
      (2 / den τ l) * ((k : ℚ) * Vn τ k (l + 1)) +
        (-2 * ((l : ℚ) + 1) / den τ l) * Vn (τ + 1) (k + 1) l := by
    funext k
    rw [Vn_succ]
    unfold den
    ring
  rw [hf, fd_lin, fd_shift (fun k => Vn (τ + 1) k l), ← fd_succ_add]
  · ring
where
  fd_succ_add : (fwdDiff (1 : ℕ))^[i] (fun k => Vn (τ + 1) k l) (0 + 1) =
      (fwdDiff (1 : ℕ))^[i] (fun k => Vn (τ + 1) k l) 0 + (fwdDiff (1 : ℕ))^[i + 1] (fun k => Vn (τ + 1) k l) 0 := by
    rw [fd_succ]
    ring

lemma T_succ_zero (τ l : ℕ) : T (τ + 1) (l + 1) 0 =
    -2 * ((l : ℚ) + 1) * (T (τ + 1) l 0 + T (τ + 1) l 1) / den τ l := by
  rw [T_succ]
  simp

lemma T_succ_succ (τ l i : ℕ) : T (τ + 1) (l + 1) (i + 1) =
    (2 * ((i : ℚ) + 1) * (T τ (l + 1) i + T τ (l + 1) (i + 1)) -
      2 * ((l : ℚ) + 1) * (T (τ + 1) l (i + 1) + T (τ + 1) l (i + 2))) / den τ l := by
  rw [T_succ, fd_zero_mul]
  unfold T
  ring

/-- Vn τ · l is a polynomial of degree ≤ τ: its differences of order > τ vanish. -/
theorem T_zero (l : ℕ) : ∀ τ i, τ < i → T τ l i = 0 := by
  induction l with
  | zero =>
    intro τ i h
    rw [T_l0, pw_big τ i h, mul_zero]
  | succ l ihl =>
    intro τ
    induction τ with
    | zero =>
      intro i h
      obtain ⟨i, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
      exact T_t0 l i
    | succ τ ihτ =>
      intro i h
      obtain ⟨i, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
      rw [T_succ_succ, ihτ i (by omega), ihτ (i + 1) (by omega), ihl (τ + 1) (i + 1) (by omega),
        ihl (τ + 1) (i + 2) (by omega)]
      ring

/-! ### The two top coefficients -/

/-- a τ l = Δ^τ Vn τ · l (0) = τ! × (coefficient of k^τ). -/
def a (τ l : ℕ) : ℚ := T τ l τ

/-- q τ l = Δ^τ Vn (τ+1) · l (0). -/
def q (τ l : ℕ) : ℚ := T (τ + 1) l τ

lemma a_l0 (τ : ℕ) : a τ 0 = cc τ * τ.factorial := by
  rw [a, T_l0, pw_diag]

lemma a_t0 (l : ℕ) : a 0 (l + 1) = 2 ^ (l + 1) * ((l : ℚ) + 1) := T_t0_zero l

lemma a_succ (τ l : ℕ) : a (τ + 1) (l + 1) =
    (2 * ((τ : ℚ) + 1) * a τ (l + 1) - 2 * ((l : ℚ) + 1) * a (τ + 1) l) / den τ l := by
  unfold a
  rw [T_succ_succ, T_zero (l + 1) τ (τ + 1) (by omega), T_zero l (τ + 1) (τ + 2) (by omega)]
  ring

lemma q_l0 (τ : ℕ) : q τ 0 = cc (τ + 1) * ((τ + 1).factorial * τ / 2) := by
  rw [q, T_l0, pw_sub]

lemma q_zero_succ (l : ℕ) : q 0 (l + 1) = -2 * ((l : ℚ) + 1) * (q 0 l + a 1 l) / den 0 l := by
  unfold q a
  rw [T_succ_zero]

lemma q_succ (τ l : ℕ) : q (τ + 1) (l + 1) =
    (2 * ((τ : ℚ) + 1) * (q τ (l + 1) + a (τ + 1) (l + 1)) -
      2 * ((l : ℚ) + 1) * (q (τ + 1) l + a (τ + 2) l)) / den (τ + 1) l := by
  unfold q a
  rw [T_succ_succ]

/-! ### S in terms of q -/

theorem S_eq (n : ℕ) : S n = -∑ i ∈ range (n + 1), (n.choose i : ℚ) * q i (n - i) := by
  unfold S
  congr 1
  refine sum_congr rfl fun i hi => ?_
  unfold q T
  rw [fwdDiff_iter_eq_sum_shift, mul_sum]
  refine sum_congr rfl fun m hm => ?_
  have hm' : m ≤ i := by simp at hm; omega
  rw [zsmul_eq_mul]
  push_cast
  have : ((-1 : ℚ) ^ (i - m)) = (-1) ^ (i + m) := by
    rw [show i + m = (i - m) + 2 * m by omega, pow_add, pow_mul]
    simp
  rw [this, smul_eq_mul, mul_one, zero_add]
  ring


/-! ### Closed forms for a and q -/

open Polynomial

/-- ι p = ∫_0^1 p(ρ) dρ, as the linear map X^n ↦ 1/(n+1). -/
noncomputable def ι : ℚ[X] →ₗ[ℚ] ℚ :=
  Polynomial.lsum (fun n => ((1 : ℚ) / ((n : ℚ) + 1)) • LinearMap.id)

lemma ι_monomial (n : ℕ) (c : ℚ) : ι (monomial n c) = c / ((n : ℚ) + 1) := by
  rw [ι, lsum_apply, sum_monomial_index]
  · simp only [LinearMap.smul_apply, LinearMap.id_apply, smul_eq_mul]
    ring
  · simp

lemma ι_X_pow (n : ℕ) : ι ((X : ℚ[X]) ^ n) = 1 / ((n : ℚ) + 1) := by
  rw [X_pow_eq_monomial, ι_monomial]

lemma ι_deriv (p : ℚ[X]) : ι (derivative p) = p.eval 1 - p.eval 0 := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, map_add, hp, hq, eval_add, eval_add]; ring
  | monomial n c =>
    rw [derivative_monomial, ι_monomial, eval_monomial, eval_monomial]
    rcases n with _ | n
    · simp
    · rw [Nat.add_sub_cancel]
      simp only [one_pow, mul_one, ne_eq, Nat.add_eq_zero_iff, one_ne_zero, and_false,
        not_false_eq_true, zero_pow, mul_zero, sub_zero]
      push_cast
      field_simp

lemma ι_two_mul (p : ℚ[X]) : ι (2 * p) = 2 * ι p := by
  rw [two_mul, map_add, two_mul]

lemma ι_nat_mul (n : ℕ) (p : ℚ[X]) : ι ((n : ℚ[X]) * p) = (n : ℚ) * ι p := by
  rw [← nsmul_eq_mul, map_nsmul, nsmul_eq_mul]

/-- I α β = ∫_0^1 ρ^(α+β) (ρ-2)^α dρ. -/
noncomputable def I (α β : ℕ) : ℚ := ι (X ^ (α + β) * (X - 2) ^ α)

lemma I_zero_left (β : ℕ) : I 0 β = 1 / ((β : ℚ) + 1) := by
  simp [I, ι_X_pow]

lemma I0 (α β : ℕ) : I (α + 1) β = I α (β + 2) - 2 * I α (β + 1) := by
  unfold I
  rw [show (X : ℚ[X]) ^ (α + 1 + β) * (X - 2) ^ (α + 1) =
      X ^ (α + (β + 2)) * (X - 2) ^ α - 2 * (X ^ (α + (β + 1)) * (X - 2) ^ α) by ring,
    map_sub, ι_two_mul]

lemma I1 (α β : ℕ) :
    (2 * (α : ℚ) + β + 2) * I α (β + 1) - 2 * ((α : ℚ) + β + 1) * I α β = (-1) ^ (α + 1) := by
  have hd : derivative ((X : ℚ[X]) ^ (α + β + 1) * (X - 2) ^ (α + 1)) =
      ((2 * α + β + 2 : ℕ) : ℚ[X]) * (X ^ (α + (β + 1)) * (X - 2) ^ α) -
        ((2 * (α + β + 1) : ℕ) : ℚ[X]) * (X ^ (α + β) * (X - 2) ^ α) := by
    rw [derivative_mul, derivative_X_pow, derivative_pow, derivative_sub, derivative_X]
    simp only [Nat.add_sub_cancel, map_natCast, derivative_ofNat, sub_zero, mul_one]
    push_cast
    ring
  have h := ι_deriv ((X : ℚ[X]) ^ (α + β + 1) * (X - 2) ^ (α + 1))
  rw [hd, map_sub, ι_nat_mul, ι_nat_mul] at h
  unfold I
  simp only [eval_mul, eval_pow, eval_X, eval_sub, eval_ofNat, one_pow, one_mul, ne_eq,
    Nat.add_eq_zero_iff, one_ne_zero, and_false, not_false_eq_true, zero_pow, zero_mul,
    sub_zero] at h
  push_cast at h
  norm_num at h
  linear_combination h

lemma I_l0 (τ : ℕ) : I τ 0 = -(cc (τ + 1) * τ.factorial) / 2 := by
  induction τ with
  | zero => simp [I_zero_left, cc]
  | succ τ ih =>
    have e0 := I0 τ 0
    have e1 := I1 τ 0
    have e2 := I1 τ 1
    push_cast at e1 e2
    have key : (2 * (τ : ℚ) + 3) * I (τ + 1) 0 = -(2 * (τ : ℚ) + 2) * I τ 0 := by
      rw [e0]
      linear_combination e2 - e1
    have hpos : (2 * (τ : ℚ) + 3) ≠ 0 := by positivity
    rw [show cc (τ + 1 + 1) = -2 * cc (τ + 1) / (2 * ((τ + 1 : ℕ) : ℚ) + 1) from rfl,
      Nat.factorial_succ]
    push_cast
    rw [ih] at key
    field_simp at key ⊢
    linear_combination key

/-- Closed form of a. -/
noncomputable def aE : ℕ → ℕ → ℚ
  | 0, 0 => 1
  | 0, l + 1 => 2 ^ (l + 1) * ((l : ℚ) + 1)
  | τ + 1, l => (-1) ^ (τ + 1) * l * 2 ^ l - 2 ^ (l + 1) * ((τ : ℚ) + 1) * I τ l

/-- Closed form of q. -/
noncomputable def qE (τ l : ℕ) : ℚ :=
  (-1) ^ τ * 2 ^ l * (-(l : ℚ) * (2 * l + 3 * τ) / 6) +
    2 ^ l * (((l : ℚ) ^ 2 - 2 * l * τ - 5 * l - 3 * τ ^ 2 - 3 * τ) / 3) * I τ l

lemma Jrel (τ l : ℕ) :
    (2 * (τ : ℚ) + l + 4) * I (τ + 1) (l + 1) + 2 * ((τ : ℚ) + 1) * I τ (l + 1) -
      ((l : ℚ) + 1) * I (τ + 1) l = 0 := by
  have e1 := I0 τ (l + 1)
  have e2 := I0 τ l
  have e3 := I1 τ (l + 2)
  have e4 := I1 τ (l + 1)
  push_cast at e3 e4
  rw [show l + 1 + 2 = l + 3 by ring, show l + 1 + 1 = l + 2 by ring] at e1
  rw [show l + 2 + 1 = l + 3 by ring] at e3
  rw [show l + 1 + 1 = l + 2 by ring] at e4
  linear_combination (2 * (τ : ℚ) + l + 4) * e1 - ((l : ℚ) + 1) * e2 + e3 - e4

lemma Krel (τ l : ℕ) :
    (2 * (τ : ℚ) + 2) * I τ (l + 1) + (2 * (τ : ℚ) + l + 3) * I (τ + 1) l = (-1) ^ (τ + 1) := by
  have e2 := I0 τ l
  have e4 := I1 τ (l + 1)
  push_cast at e4
  rw [show l + 1 + 1 = l + 2 by ring] at e4
  linear_combination (2 * (τ : ℚ) + l + 3) * e2 + e4

theorem a_eq (l : ℕ) : ∀ τ, a τ l = aE τ l := by
  induction l with
  | zero =>
    intro τ
    rw [a_l0]
    rcases τ with _ | τ
    · simp [aE, cc]
    · simp only [aE, CharP.cast_eq_zero, mul_zero, zero_mul, pow_zero, zero_add, pow_one, zero_sub]
      rw [I_l0, Nat.factorial_succ]
      push_cast
      ring
  | succ l ihl =>
    intro τ
    induction τ with
    | zero => rw [a_t0]; simp [aE]
    | succ τ ihτ =>
      rw [a_succ, ihτ, ihl, div_eq_iff (den_ne τ l), eq_comm]
      rcases τ with _ | τ
      · simp only [aE, I_zero_left, den]
        push_cast
        field_simp
        ring
      · simp only [aE, den]
        push_cast
        linear_combination (2 ^ (l + 2) * ((τ : ℚ) + 2)) * Jrel τ l

theorem q_eq (l : ℕ) : ∀ τ, q τ l = qE τ l := by
  induction l with
  | zero =>
    intro τ
    rw [q_l0, qE, I_l0, Nat.factorial_succ]
    push_cast
    ring
  | succ l ihl =>
    intro τ
    induction τ with
    | zero =>
      rw [q_zero_succ, ihl, a_eq, div_eq_iff (den_ne 0 l), eq_comm]
      simp only [qE, aE, I_zero_left, den]
      push_cast
      field_simp
      ring
    | succ τ ihτ =>
      rw [q_succ, ihτ, ihl, a_eq, a_eq, div_eq_iff (den_ne (τ + 1) l), eq_comm]
      simp only [qE, aE, den]
      push_cast
      linear_combination
        (2 * 2 ^ l * (-(l : ℚ) ^ 2 + 2 * l * τ + 5 * l + 3 * τ ^ 2 + 11 * τ + 12) / 3) *
          Jrel τ l + (-4 * 2 ^ l * ((l : ℚ) + 1) / 3) * Krel τ l

/-! ### Binomial moments and the diagonal sum -/

lemma B0 {R : Type*} [CommRing R] (n : ℕ) (Y Z : R) :
    ∑ i ∈ range (n + 1), (n.choose i : R) * Y ^ i * Z ^ (n - i) = (Y + Z) ^ n := by
  rw [add_pow]
  refine sum_congr rfl fun i _ => ?_
  ring

lemma B1 {R : Type*} [CommRing R] (n : ℕ) (Y Z : R) :
    ∑ i ∈ range (n + 1), (n.choose i : R) * i * Y ^ i * Z ^ (n - i) =
      n * Y * (Y + Z) ^ (n - 1) := by
  rcases n with _ | m
  · simp
  · rw [sum_range_succ', Nat.add_sub_cancel, ← B0 m Y Z, mul_sum]
    simp only [Nat.cast_zero, mul_zero, zero_mul, add_zero]
    refine sum_congr rfl fun j hj => ?_
    have hc : ((m + 1).choose (j + 1) : R) * ((j : R) + 1) = ((m : R) + 1) * (m.choose j) := by
      have := congrArg (Nat.cast : ℕ → R) (Nat.add_one_mul_choose_eq m j)
      push_cast at this
      linear_combination (-1 : R) * this
    rw [show m + 1 - (j + 1) = m - j by omega]
    push_cast
    linear_combination (Y ^ (j + 1) * Z ^ (m - j)) * hc

lemma B2 {R : Type*} [CommRing R] (n : ℕ) (Y Z : R) :
    ∑ i ∈ range (n + 1), (n.choose i : R) * (i * ((i : R) - 1)) * Y ^ i * Z ^ (n - i) =
      n * ((n : R) - 1) * Y ^ 2 * (Y + Z) ^ (n - 2) := by
  rcases n with _ | m
  · simp
  · rw [sum_range_succ']
    simp only [Nat.cast_zero, zero_mul, mul_zero, zero_mul, add_zero]
    have h1 := B1 m Y Z
    have e : ∀ j ∈ range (m + 1), ((m + 1).choose (j + 1) : R) * (((j + 1 : ℕ) : R) *
        (((j + 1 : ℕ) : R) - 1)) * Y ^ (j + 1) * Z ^ (m + 1 - (j + 1)) =
        ((m : R) + 1) * Y * ((m.choose j : R) * j * Y ^ j * Z ^ (m - j)) := by
      intro j _
      have hc : ((m + 1).choose (j + 1) : R) * ((j : R) + 1) = ((m : R) + 1) * (m.choose j) := by
        have := congrArg (Nat.cast : ℕ → R) (Nat.add_one_mul_choose_eq m j)
        push_cast at this
        linear_combination (-1 : R) * this
      rw [show m + 1 - (j + 1) = m - j by omega]
      push_cast
      linear_combination ((j : R) * Y ^ (j + 1) * Z ^ (m - j)) * hc
    rw [sum_congr rfl e, ← mul_sum, h1]
    rcases m with _ | k
    · simp
    · push_cast
      ring

lemma I_diag (n i : ℕ) (hi : i ≤ n) : I i (n - i) = ι (X ^ n * (X - 2) ^ i) := by
  unfold I
  rw [Nat.add_sub_cancel' hi]

lemma ι_sum (n : ℕ) (c : ℕ → ℚ) :
    ∑ i ∈ range (n + 1), c i * ι (X ^ n * (X - 2) ^ i) =
      ι (∑ i ∈ range (n + 1), c i • ((X : ℚ[X]) ^ n * (X - 2) ^ i)) := by
  rw [map_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [map_smul, smul_eq_mul]

lemma diag0 (n : ℕ) :
    ∑ i ∈ range (n + 1), (n.choose i : ℚ) * 2 ^ (n - i) * I i (n - i) = 1 / (2 * (n : ℚ) + 1) := by
  rw [sum_congr rfl fun i hi => by rw [I_diag n i (by simp at hi; omega)], ι_sum]
  have hpoly : ∑ i ∈ range (n + 1), ((n.choose i : ℚ) * 2 ^ (n - i)) •
      ((X : ℚ[X]) ^ n * (X - 2) ^ i) = X ^ (2 * n) := by
    have h := B0 n ((X : ℚ[X]) - 2) 2
    rw [show (X : ℚ[X]) - 2 + 2 = X by ring] at h
    rw [show (X : ℚ[X]) ^ (2 * n) = X ^ n * X ^ n by ring, ← h, mul_sum]
    refine sum_congr rfl fun i _ => ?_
    rw [smul_eq_C_mul]
    simp only [map_mul, map_pow, map_natCast, map_ofNat]
    ring
  rw [hpoly, ι_X_pow]
  push_cast
  ring

lemma diag1 (m : ℕ) :
    ∑ i ∈ range (m + 2), ((m + 1).choose i : ℚ) * i * 2 ^ (m + 1 - i) * I i (m + 1 - i) =
      ((m : ℚ) + 1) / (2 * ((m : ℚ) + 1) + 1) - 1 := by
  rw [sum_congr rfl fun i hi => by rw [I_diag (m + 1) i (by simp at hi; omega)], ι_sum]
  have hpoly : ∑ i ∈ range (m + 2), (((m + 1).choose i : ℚ) * i * 2 ^ (m + 1 - i)) •
      ((X : ℚ[X]) ^ (m + 1) * (X - 2) ^ i) =
      ((m + 1 : ℕ) : ℚ[X]) * X ^ (2 * m + 2) - 2 * (((m + 1 : ℕ) : ℚ[X]) * X ^ (2 * m + 1)) := by
    have h := B1 (m + 1) ((X : ℚ[X]) - 2) 2
    rw [show (X : ℚ[X]) - 2 + 2 = X by ring, Nat.add_sub_cancel] at h
    have h2 : ((m + 1 : ℕ) : ℚ[X]) * X ^ (2 * m + 2) - 2 * (((m + 1 : ℕ) : ℚ[X]) * X ^ (2 * m + 1)) =
        X ^ (m + 1) * (((m + 1 : ℕ) : ℚ[X]) * (X - 2) * X ^ m) := by ring
    rw [h2, ← h, mul_sum]
    refine sum_congr rfl fun i _ => ?_
    rw [smul_eq_C_mul]
    simp only [map_mul, map_pow, map_natCast, map_ofNat]
    ring
  rw [hpoly, map_sub, ι_two_mul, ι_nat_mul, ι_nat_mul, ι_X_pow, ι_X_pow]
  push_cast
  field_simp
  ring

/-- The diagonal sum of the closed form of q. -/
theorem diag_qE (m : ℕ) :
    ∑ i ∈ range (m + 2), ((m + 1).choose i : ℚ) * qE i (m + 1 - i) =
      -(2 / 3 * (((m : ℚ) + 1) ^ 3 - ((m : ℚ) + 1) ^ 2 + 2 * ((m : ℚ) + 1) + 1) /
        (2 * ((m : ℚ) + 1) + 1)) := by
  set n := m + 1 with hn
  have hterm : ∀ i ∈ range (n + 1), (n.choose i : ℚ) * qE i (n - i) =
      -(1 / 6) * (2 * (n : ℚ) ^ 2 * ((n.choose i : ℚ) * (-1) ^ i * 2 ^ (n - i)) -
        ((n : ℚ) + 1) * ((n.choose i : ℚ) * i * (-1) ^ i * 2 ^ (n - i)) -
        ((n.choose i : ℚ) * (i * ((i : ℚ) - 1)) * (-1) ^ i * 2 ^ (n - i))) +
      (((n : ℚ) ^ 2 - 5 * n) / 3) * ((n.choose i : ℚ) * 2 ^ (n - i) * I i (n - i)) +
      ((2 - 4 * (n : ℚ)) / 3) * ((n.choose i : ℚ) * i * 2 ^ (n - i) * I i (n - i)) := by
    intro i hi
    have hi' : i ≤ n := by simp at hi; omega
    unfold qE
    rw [Nat.cast_sub hi']
    ring
  rw [sum_congr rfl hterm, sum_add_distrib, sum_add_distrib, ← mul_sum, ← mul_sum, ← mul_sum,
    sum_sub_distrib, sum_sub_distrib, ← mul_sum, ← mul_sum]
  rw [B0 n (-1 : ℚ) 2, B1 n (-1 : ℚ) 2, B2 n (-1 : ℚ) 2, diag0, hn, diag1]
  norm_num
  field_simp
  ring

/-- **A103990 (McGarvey's conjecture), under the reading of Trott's integrand.**
√π I(n,0) = (2/3)(n^3 - n^2 + 2n + 1)/(2n + 1) for n ≥ 1. -/
theorem A103990_main (n : ℕ) (hn : 1 ≤ n) :
    S n = 2 / 3 * ((n : ℚ) ^ 3 - (n : ℚ) ^ 2 + 2 * n + 1) / (2 * n + 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [S_eq, sum_congr rfl fun i _ => by rw [q_eq], diag_qE]
  push_cast
  field_simp

/-! ### The value functional on all monomials (Argument 1-2)

Monomials t^j X^k W^l, j ∈ ℤ. For h = u t^j X^k W^l the derivative is
(1 + 2j - l) t^j X^k W^l - 2k t^(j+1) X^k W^l + 2l t^j X^(k+1) W^(l-1); h is an
allowed integration-by-parts function unless k = 0 and l = 2j + 1 (h = erf^l).
The canonical basis is X^(g-l) W^l t^(l/2) (0 ≤ l < g), with value at u = 0
equal to `anc l` (1, 2, 0, ... since X(0) = 1, W(0) = 2). -/

/-- Value at 0 of the basis element with W-degree l. -/
def anc (l : ℕ) : ℚ := if l = 0 then 1 else if l = 1 then 2 else 0

/-- Position j = ⌊l/2⌋ of the basis element with W-degree l. -/
def j0 (l : ℕ) : ℤ := ((l / 2 : ℕ) : ℤ)

/-- V on t^j X^k (l = 0). -/
def G (j : ℤ) (k : ℕ) : ℚ :=
  if hk : k = 0 then 0
  else if hj : j = 0 then 1
  else if hp : 0 < j then (2 * ((j : ℚ) - 1) + 1) * G (j - 1) k / (2 * k)
  else 2 * k * G (j + 1) k / (1 + 2 * (j : ℚ))
termination_by j.natAbs
decreasing_by all_goals omega

/-- V on t^j X^k W^l, solved from the anchors upwards and downwards in j. -/
def V : ℕ → ℤ → ℕ → ℚ
  | 0, j, k => G j k
  | l + 1, j, k =>
    if hk : k = 0 then
      (if 2 * j + 1 = ((l + 1 : ℕ) : ℤ) then 0
       else -2 * ((l : ℚ) + 1) * V l j 1 / (1 + 2 * (j : ℚ) - ((l : ℚ) + 1)))
    else if hj : j = (((l + 1) / 2 : ℕ) : ℤ) then anc (l + 1)
    else if hp : (((l + 1) / 2 : ℕ) : ℤ) < j then
      ((1 + 2 * ((j : ℚ) - 1) - ((l : ℚ) + 1)) * V (l + 1) (j - 1) k +
        2 * ((l : ℚ) + 1) * V l (j - 1) (k + 1)) / (2 * k)
    else
      (2 * k * V (l + 1) (j + 1) k - 2 * ((l : ℚ) + 1) * V l j (k + 1)) /
        (1 + 2 * (j : ℚ) - ((l : ℚ) + 1))
termination_by l j _ => (l, (j - ((l / 2 : ℕ) : ℤ)).natAbs)
decreasing_by
  all_goals simp_wf
  all_goals first
    | (apply Prod.Lex.left; omega)
    | (apply Prod.Lex.right; omega)

lemma G_eq (j : ℤ) (k : ℕ) : G j k =
    if k = 0 then 0 else if j = 0 then 1
    else if 0 < j then (2 * ((j : ℚ) - 1) + 1) * G (j - 1) k / (2 * k)
    else 2 * k * G (j + 1) k / (1 + 2 * (j : ℚ)) := by
  rw [G]
  simp only [dite_eq_ite]

lemma G_rel (j : ℤ) (k : ℕ) : (1 + 2 * (j : ℚ)) * G j k - 2 * k * G (j + 1) k = 0 := by
  by_cases hk : k = 0
  · subst hk
    rw [G_eq, G_eq (j + 1)]
    simp
  have hk' : (k : ℚ) ≠ 0 := by exact_mod_cast hk
  rcases lt_or_ge j 0 with hj | hj
  · have h1 : j ≠ 0 := by omega
    have h2 : ¬ (0 < j) := by omega
    rw [G_eq j k]
    simp only [hk, h1, h2, ↓reduceIte]
    have : (j : ℚ) ≤ -1 := by exact_mod_cast (by omega : j ≤ -1)
    have : (1 + 2 * (j : ℚ)) ≠ 0 := by linarith
    field_simp
    ring
  · have h1 : j + 1 ≠ 0 := by omega
    have h2 : 0 < j + 1 := by omega
    rw [G_eq (j + 1) k]
    simp only [hk, h1, h2, ↓reduceIte, add_sub_cancel_right]
    push_cast
    field_simp
    ring

lemma V_zero (j : ℤ) (k : ℕ) : V 0 j k = G j k := by
  rw [V]

lemma V_succ_eq (l : ℕ) (j : ℤ) (k : ℕ) : V (l + 1) j k =
    if k = 0 then
      (if 2 * j + 1 = ((l + 1 : ℕ) : ℤ) then 0
       else -2 * ((l : ℚ) + 1) * V l j 1 / (1 + 2 * (j : ℚ) - ((l : ℚ) + 1)))
    else if j = (((l + 1) / 2 : ℕ) : ℤ) then anc (l + 1)
    else if (((l + 1) / 2 : ℕ) : ℤ) < j then
      ((1 + 2 * ((j : ℚ) - 1) - ((l : ℚ) + 1)) * V (l + 1) (j - 1) k +
        2 * ((l : ℚ) + 1) * V l (j - 1) (k + 1)) / (2 * k)
    else
      (2 * k * V (l + 1) (j + 1) k - 2 * ((l : ℚ) + 1) * V l j (k + 1)) /
        (1 + 2 * (j : ℚ) - ((l : ℚ) + 1)) := by
  rw [V]
  simp only [dite_eq_ite]

/-- V kills every allowed integration-by-parts relation at level l + 1. -/
lemma V_rel (l : ℕ) (j : ℤ) (k : ℕ) (hall : ¬ (k = 0 ∧ 2 * j + 1 = ((l + 1 : ℕ) : ℤ))) :
    (1 + 2 * (j : ℚ) - ((l : ℚ) + 1)) * V (l + 1) j k - 2 * k * V (l + 1) (j + 1) k +
      2 * ((l : ℚ) + 1) * V l j (k + 1) = 0 := by
  by_cases hk : k = 0
  · subst hk
    have hne : 2 * j + 1 ≠ ((l + 1 : ℕ) : ℤ) := fun h => hall ⟨rfl, h⟩
    have hden : (1 + 2 * (j : ℚ) - ((l : ℚ) + 1)) ≠ 0 := by
      intro h
      apply hne
      have : ((2 * j + 1 : ℤ) : ℚ) = (((l + 1 : ℕ) : ℤ) : ℚ) := by push_cast; linarith
      exact_mod_cast this
    rw [V_succ_eq l j 0]
    simp only [hne, ↓reduceIte]
    field_simp
    ring
  have hk' : (k : ℚ) ≠ 0 := by exact_mod_cast hk
  rcases lt_or_ge j (((l + 1) / 2 : ℕ) : ℤ) with hj | hj
  · have h1 : j ≠ (((l + 1) / 2 : ℕ) : ℤ) := by omega
    have h2 : ¬ ((((l + 1) / 2 : ℕ) : ℤ) < j) := by omega
    have hden : (1 + 2 * (j : ℚ) - ((l : ℚ) + 1)) ≠ 0 := by
      have : 2 * j + 2 ≤ ((l + 1 : ℕ) : ℤ) := by omega
      have : 2 * (j : ℚ) + 2 ≤ (l : ℚ) + 1 := by exact_mod_cast this
      linarith
    rw [V_succ_eq l j k]
    simp only [hk, h1, h2, ↓reduceIte]
    field_simp
    ring
  · have h1 : j + 1 ≠ (((l + 1) / 2 : ℕ) : ℤ) := by omega
    have h2 : (((l + 1) / 2 : ℕ) : ℤ) < j + 1 := by omega
    rw [V_succ_eq l (j + 1) k]
    simp only [hk, h1, h2, ↓reduceIte, add_sub_cancel_right]
    push_cast
    field_simp
    ring

lemma V_anchor (l k : ℕ) (hk : 1 ≤ k) : V l (((l / 2 : ℕ) : ℤ)) k = anc l := by
  rcases l with _ | l
  · rw [V_zero, G_eq]
    simp [show k ≠ 0 by omega, anc]
  · rw [V_succ_eq]
    simp [show k ≠ 0 by omega]

/-- V vanishes strictly between j = 0 and the anchor. -/
lemma V_mid (l : ℕ) : ∀ k, 1 ≤ k → ∀ d : ℕ, ∀ j : ℤ, j + d = ((l / 2 : ℕ) : ℤ) → 1 ≤ j →
    V l j k = 0 := by
  induction l with
  | zero => intro k _ d j hj h1; simp at hj; omega
  | succ l ih =>
    intro k hk d
    induction d with
    | zero =>
      intro j hj h1
      simp only [Nat.cast_zero, add_zero] at hj
      subst hj
      rw [V_anchor _ _ hk, anc]
      have hl : l ≠ 0 := by omega
      simp [hl]
    | succ d ihd =>
      intro j hj h1
      have hr := V_rel l j k (by omega)
      have e1 : V (l + 1) (j + 1) k = 0 := ihd (j + 1) (by push_cast at hj ⊢; omega) (by omega)
      have e2 : V l j (k + 1) = 0 := ih (k + 1) (by omega) ((l / 2) - j.toNat) j
        (by omega) h1
      rw [e1, e2] at hr
      have hden : (1 + 2 * (j : ℚ) - ((l : ℚ) + 1)) ≠ 0 := by
        have : 2 * j + 2 ≤ ((l + 1 : ℕ) : ℤ) := by push_cast at hj; omega
        have : 2 * (j : ℚ) + 2 ≤ (l : ℚ) + 1 := by exact_mod_cast this
        linarith
      have : (1 + 2 * (j : ℚ) - ((l : ℚ) + 1)) * V (l + 1) j k = 0 := by linarith
      exact (mul_eq_zero.1 this).resolve_left hden

lemma V_at_zero (l k : ℕ) (h : 1 ≤ k ∨ 1 ≤ l) : V (l + 1) 0 k = 2 ^ (l + 1) * ((l : ℚ) + 1) := by
  induction l generalizing k with
  | zero =>
    have hk : 1 ≤ k := by omega
    have := V_anchor 1 k hk
    simpa [anc] using this
  | succ l ih =>
    have hr := V_rel (l + 1) 0 k (by intro h; omega)
    have hmid : 2 * (k : ℚ) * V (l + 1 + 1) 1 k = 0 := by
      rcases Nat.eq_zero_or_pos k with h0 | hpos
      · subst h0; simp
      · rw [V_mid (l + 1 + 1) k hpos ((l + 1 + 1) / 2 - 1) 1 (by omega) (by norm_num)]
        ring
    rw [ih (k + 1) (by omega), zero_add] at hr
    push_cast at hr ⊢
    have key : ((l : ℚ) + 1) * V (l + 1 + 1) 0 k =
        ((l : ℚ) + 1) * (2 ^ (l + 1 + 1) * ((l : ℚ) + 1 + 1)) := by
      linear_combination (-1 : ℚ) * hr - hmid
    have hl : ((l : ℚ) + 1) ≠ 0 := by positivity
    exact mul_left_cancel₀ hl key

lemma G_neg (τ k : ℕ) (h : 1 ≤ τ ∨ 1 ≤ k) : G (-(τ : ℤ)) k = cc τ * (k : ℚ) ^ τ := by
  induction τ with
  | zero =>
    have hk : k ≠ 0 := by omega
    rw [G_eq]
    simp [hk, cc]
  | succ τ ih =>
    rcases Nat.eq_zero_or_pos k with h0 | hpos
    · subst h0
      rw [G_eq]
      simp
    · have hr := G_rel (-((τ + 1 : ℕ) : ℤ)) k
      rw [show -((τ + 1 : ℕ) : ℤ) + 1 = -(τ : ℤ) by push_cast; ring, ih (Or.inr hpos)] at hr
      push_cast at hr
      have hd : (2 * (τ : ℚ) + 1) ≠ 0 := by positivity
      rw [show cc (τ + 1) = -2 * cc τ / (2 * τ + 1) from rfl]
      push_cast
      field_simp
      linear_combination (-1 : ℚ) * hr

/-- The recursion `Vn` is V below the anchors. -/
theorem Vn_eq (l : ℕ) : ∀ τ k, (1 ≤ τ ∨ 1 ≤ k ∨ 2 ≤ l) → Vn τ k l = V l (-(τ : ℤ)) k := by
  induction l with
  | zero =>
    intro τ k h
    rw [Vn_l0, V_zero, G_neg τ k (by omega)]
  | succ l ihl =>
    intro τ
    induction τ with
    | zero =>
      intro k h
      rw [Vn_t0, Nat.cast_zero, neg_zero, V_at_zero l k (by omega)]
    | succ τ ihτ =>
      intro k h
      have hr := V_rel l (-((τ + 1 : ℕ) : ℤ)) k (by omega)
      rw [show -((τ + 1 : ℕ) : ℤ) + 1 = -(τ : ℤ) by push_cast; ring] at hr
      have e : 2 * (k : ℚ) * V (l + 1) (-(τ : ℤ)) k = 2 * k * Vn τ k (l + 1) := by
        rcases Nat.eq_zero_or_pos k with h0 | hpos
        · subst h0; simp
        · rw [ihτ k (by omega)]
      have hi := ihl (τ + 1) (k + 1) (by omega)
      have hd := den_ne τ l
      unfold den at hd
      rw [Vn_succ, div_eq_iff hd]
      push_cast at hr hi ⊢
      linear_combination (-1 : ℚ) * hr - e - 2 * ((l : ℚ) + 1) * hi

/-! ### Canonical forms in the formal model -/

/-- Monomials t^j X^k W^l, indexed by (j, k, l). -/
abbrev Mon := ℤ × ℕ × ℕ

/-- V extended linearly to finite combinations of monomials. -/
noncomputable def VL : (Mon →₀ ℚ) →ₗ[ℚ] ℚ :=
  Finsupp.lsum ℚ (fun m : Mon => (V m.2.2 m.1 m.2.1) • LinearMap.id)

lemma VL_single (m : Mon) (c : ℚ) : VL (Finsupp.single m c) = V m.2.2 m.1 m.2.1 * c := by
  simp [VL]

/-- D(u t^j X^k W^l) in monomials. -/
noncomputable def rel (j : ℤ) (k l : ℕ) : Mon →₀ ℚ :=
  Finsupp.single (j, k, l) (1 + 2 * (j : ℚ) - l) - Finsupp.single (j + 1, k, l) (2 * (k : ℚ)) +
    Finsupp.single (j, k + 1, l - 1) (2 * (l : ℚ))

/-- The allowed integration-by-parts relations (h ≠ erf^l). -/
def Rels : Set (Mon →₀ ℚ) :=
  {r | ∃ (j : ℤ) (k l : ℕ), ¬ (k = 0 ∧ 2 * j + 1 = ((l : ℕ) : ℤ)) ∧ r = rel j k l}

lemma VL_rel : ∀ r ∈ Rels, VL r = 0 := by
  rintro r ⟨j, k, l, hall, rfl⟩
  simp only [rel, map_add, map_sub, VL_single]
  rcases l with _ | l
  · simp only [V_zero, Nat.cast_zero, mul_zero, sub_zero]
    linear_combination G_rel j k
  · have := V_rel l j k (by push_cast at hall ⊢; exact hall)
    simp only [Nat.add_sub_cancel]
    push_cast
    linear_combination this

/-- (1 - d^n)/t in monomials: t^-1 - Σ C(n,i) C(i,m) (-1)^(i+m) t^-(i+1) X^m W^(n-i). -/
noncomputable def Fn (n : ℕ) : Mon →₀ ℚ :=
  Finsupp.single (-1, 0, 0) 1 - ∑ i ∈ range (n + 1), ∑ m ∈ range (i + 1),
    Finsupp.single (-((i + 1 : ℕ) : ℤ), m, n - i)
      ((n.choose i : ℚ) * (i.choose m) * (-1) ^ (i + m))

lemma VL_Fn (n : ℕ) : VL (Fn n) = S n := by
  simp only [Fn, map_sub, map_sum, VL_single, S]
  rw [show V 0 (-1) 0 = 0 by rw [V_zero, G_eq]; simp]
  simp only [zero_mul, zero_sub]
  congr 1
  refine sum_congr rfl fun i _ => sum_congr rfl fun m _ => ?_
  rw [Vn_eq (n - i) (i + 1) m (by omega)]
  ring

/-- **Canonical value.** If a combination of basis elements X^k W^l t^(l/2) (k ≥ 1)
differs from (1 - d^n)/t by allowed integration-by-parts relations, its value at u = 0
is (2/3)(n^3 - n^2 + 2n + 1)/(2n + 1). -/
theorem A103990_canonical (n : ℕ) (hn : 1 ≤ n) (B : Finset (ℕ × ℕ)) (hB : ∀ p ∈ B, 1 ≤ p.1)
    (c : ℕ × ℕ → ℚ)
    (h : Fn n - ∑ p ∈ B, Finsupp.single (((p.2 / 2 : ℕ) : ℤ), p.1, p.2) (c p) ∈
      Submodule.span ℚ Rels) :
    ∑ p ∈ B, c p * anc p.2 = 2 / 3 * ((n : ℚ) ^ 3 - (n : ℚ) ^ 2 + 2 * n + 1) / (2 * n + 1) := by
  have hker : Submodule.span ℚ Rels ≤ LinearMap.ker VL :=
    Submodule.span_le.2 fun r hr => LinearMap.mem_ker.2 (VL_rel r hr)
  have h0 := LinearMap.mem_ker.1 (hker h)
  rw [map_sub, map_sum, VL_Fn, A103990_main n hn] at h0
  have hb : ∑ p ∈ B, VL (Finsupp.single (((p.2 / 2 : ℕ) : ℤ), p.1, p.2) (c p)) =
      ∑ p ∈ B, c p * anc p.2 := by
    refine sum_congr rfl fun p hp => ?_
    rw [VL_single]
    simp only
    rw [V_anchor p.2 p.1 (hB p hp)]
    ring
  rw [hb] at h0
  linear_combination -h0
