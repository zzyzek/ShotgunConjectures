import Mathlib

/-!
# q-series identities: Gaussian binomials and the Jacobi triple product

Definitions.
* `gauss Q N k` : the Gaussian binomial `[N, k]` evaluated at `Q` in a commutative ring, with an
  integer lower index (zero outside `0..N`), defined by q-Pascal
  `[N+1, k] = [N, k-1] + Q^k [N, k]` (`gauss_succ`).
* `tri t = t(t+1)/2`, `tri' t = t(t-1)/2` (`tri_eq`, `tri'_eq`), and `jc x y j`, the term
  `(-1)^j x^(j(j+1)/2) y^(j(j-1)/2)` of the triple product sum, for `j ∈ ℤ`
  (`jc_nat`, `jc_negSucc`).
* `jtpFactor a b i = (1 - q^(m(i+1))) (1 - q^(mi+a)) (1 - q^(mi+b))` with `m = a + b`, and
  `jtpSeries a b`, the power series `Σ_{j ∈ ℤ} (-1)^j q^(a j(j+1)/2 + b j(j-1)/2)`
  (`coeff_jtpSeries`).

Main results.
* `gauss_rule2` (the second q-Pascal rule), `gauss_two_step`, `gauss_mul_poch`
  (`[N, K] (Q;Q)_K = (Q^(N-K+1); Q)_K`).
* `jtp_finite` : the finite triple product, for any `x y` in a commutative ring and `Q = x y`,
  `∏_{i<n} (1 - x Q^i)(1 - y Q^i) = Σ_j (-1)^j x^(j(j+1)/2) y^(j(j-1)/2) [2n, n+j]_Q`,
  by induction on `n` with `gauss_two_step`.
* `jtp_mod` / `jtp_coeff` : truncations; for `k < n` the coefficient of `q^k` in
  `∏_{i<n} jtpFactor a b i` equals that of `jtpSeries a b` (`a, b ≥ 1`).
* `jacobi_triple_product` : `HasProd (jtpFactor a b) (jtpSeries a b)` in `R⟦X⟧` with the
  coefficientwise (pi) topology, i.e.
  `∏_{n ≥ 1} (1 - q^(mn)) (1 - q^(mn-b)) (1 - q^(mn-a)) = Σ_{j ∈ ℤ} (-1)^j q^(a j(j+1)/2 + b j(j-1)/2)`.
  (`a = 2, b = 1` is Euler's pentagonal theorem.)
* `hasProd_of_coeff` : a product of factors `≡ 1 mod X^(i+1)` has a value once its truncated
  coefficients are known.

All proofs are algebraic (q-Pascal induction, then truncation mod `X^N`); nothing analytic.
-/

namespace OpenProblemsLib.QSeries

open Finset PowerSeries

/-! ## Gaussian binomials -/

section Gauss

variable {R : Type*} [CommRing R]

/-- Gaussian binomial `[N, k]` evaluated at `Q`, integer lower index, by q-Pascal. -/
def gauss (Q : R) : ℕ → ℤ → R
  | 0, k => if k = 0 then 1 else 0
  | N + 1, k => gauss Q N (k - 1) + Q ^ k.toNat * gauss Q N k

theorem gauss_succ (Q : R) (N : ℕ) (k : ℤ) :
    gauss Q (N + 1) k = gauss Q N (k - 1) + Q ^ k.toNat * gauss Q N k := rfl

theorem gauss_eq_zero (Q : R) (N : ℕ) (k : ℤ) (h : k < 0 ∨ (N : ℤ) < k) : gauss Q N k = 0 := by
  induction N generalizing k with
  | zero =>
    simp only [gauss]
    split_ifs with h0
    · exact absurd h0 (by omega)
    · rfl
  | succ N ih => rw [gauss_succ, ih _ (by omega), ih _ (by omega)]; ring

theorem gauss_ne (Q : R) (N : ℕ) (k : ℤ) (h : gauss Q N k ≠ 0) : 0 ≤ k ∧ k ≤ N := by
  by_contra h'
  exact h (gauss_eq_zero Q N k (by omega))

theorem gauss_ne_of_mul (Q c : R) (N : ℕ) (k : ℤ) (h : c * gauss Q N k ≠ 0) : 0 ≤ k ∧ k ≤ N :=
  gauss_ne Q N k (fun h0 => h (by rw [h0, mul_zero]))

theorem gauss_zero_right (Q : R) (N : ℕ) : gauss Q N 0 = 1 := by
  induction N with
  | zero => simp [gauss]
  | succ N ih => rw [gauss_succ, ih, gauss_eq_zero Q N (0 - 1) (by omega)]; simp

/-- The second q-Pascal rule `[N+1, k] = Q^(N+1-k) [N, k-1] + [N, k]`. -/
theorem gauss_rule2 (Q : R) (N : ℕ) (k : ℤ) :
    gauss Q (N + 1) k = Q ^ ((N : ℤ) + 1 - k).toNat * gauss Q N (k - 1) + gauss Q N k := by
  induction N generalizing k with
  | zero =>
    simp only [gauss]
    by_cases h0 : k = 0
    · subst h0; simp
    by_cases h1 : k = 1
    · subst h1; simp
    simp [h0, show k - 1 ≠ 0 by omega]
  | succ N ih =>
    have e1 := ih (k - 1)
    have e2 := ih k
    have f1 := gauss_succ Q N (k - 1)
    have f2 := gauss_succ Q N k
    rw [show (N : ℤ) + 1 - (k - 1) = ((N + 1 : ℕ) : ℤ) + 1 - k by push_cast; ring] at e1
    have key : Q ^ k.toNat * Q ^ ((N : ℤ) + 1 - k).toNat * gauss Q N (k - 1) =
        Q ^ (((N + 1 : ℕ) : ℤ) + 1 - k).toNat * Q ^ (k - 1).toNat * gauss Q N (k - 1) := by
      by_cases hk : 1 ≤ k ∧ k ≤ N + 1
      · rw [← pow_add, ← pow_add]; congr 2; push_cast; omega
      · rw [gauss_eq_zero Q N (k - 1) (by omega)]; ring
    rw [gauss_succ Q (N + 1) k]
    linear_combination e1 + Q ^ k.toNat * e2 - Q ^ (((N + 1 : ℕ) : ℤ) + 1 - k).toNat * f1 - f2 + key

/-- Two steps of q-Pascal:
`[N+2, k] = Q^(N+2-k) [N, k-2] + (1 + Q^(N+1)) [N, k-1] + Q^k [N, k]`. -/
theorem gauss_two_step (Q : R) (N : ℕ) (k : ℤ) :
    gauss Q (N + 2) k = Q ^ ((N : ℤ) + 2 - k).toNat * gauss Q N (k - 2) +
      (1 + Q ^ (N + 1)) * gauss Q N (k - 1) + Q ^ k.toNat * gauss Q N k := by
  have e := gauss_rule2 Q (N + 1) k
  have f1 := gauss_succ Q N (k - 1)
  have f2 := gauss_succ Q N k
  rw [show k - 1 - 1 = k - 2 by ring] at f1
  rw [show ((N + 1 : ℕ) : ℤ) + 1 - k = (N : ℤ) + 2 - k by push_cast; ring] at e
  have key : Q ^ ((N : ℤ) + 2 - k).toNat * Q ^ (k - 1).toNat * gauss Q N (k - 1) =
      Q ^ (N + 1) * gauss Q N (k - 1) := by
    by_cases hk : 1 ≤ k ∧ k ≤ N + 1
    · rw [← pow_add]; congr 2; omega
    · rw [gauss_eq_zero Q N (k - 1) (by omega)]; ring
  rw [e]
  linear_combination Q ^ ((N : ℤ) + 2 - k).toNat * f1 + f2 + key

/-- Ratio of neighbouring Gaussian binomials. -/
theorem gauss_ratio (Q : R) (N K : ℕ) (hK : K ≤ N) :
    gauss Q N ((K : ℤ) + 1) * (1 - Q ^ (K + 1)) = gauss Q N K * (1 - Q ^ (N - K)) := by
  have e1 := gauss_succ Q N ((K : ℤ) + 1)
  have e2 := gauss_rule2 Q N ((K : ℤ) + 1)
  rw [show (K : ℤ) + 1 - 1 = K by ring, show ((K : ℤ) + 1).toNat = K + 1 by omega] at e1
  rw [show (K : ℤ) + 1 - 1 = K by ring,
    show ((N : ℤ) + 1 - ((K : ℤ) + 1)).toNat = N - K by omega] at e2
  linear_combination e1 - e2

/-- `[N, K] (Q;Q)_K = (1 - Q^(N-K+1)) ... (1 - Q^N)`. -/
theorem gauss_mul_poch (Q : R) (N K : ℕ) (hK : K ≤ N) :
    gauss Q N K * ∏ i ∈ range K, (1 - Q ^ (i + 1)) = ∏ i ∈ range K, (1 - Q ^ (N - K + 1 + i)) := by
  induction K with
  | zero => simp [gauss_zero_right]
  | succ K ih =>
    have h := gauss_ratio Q N K (by omega)
    push_cast
    rw [prod_range_succ, prod_range_succ']
    have e : ∀ i ∈ range K, (1 - Q ^ (N - (K + 1) + 1 + (i + 1))) = (1 - Q ^ (N - K + 1 + i)) := by
      intro i _; congr 2; omega
    rw [prod_congr rfl e, show N - (K + 1) + 1 + 0 = N - K by omega, ← ih (by omega)]
    linear_combination (∏ i ∈ range K, (1 - Q ^ (i + 1))) * h

end Gauss

/-! ## The finite triple product -/

section Finite

variable {R : Type*} [CommRing R]

/-- `tri t = t(t+1)/2`. -/
def tri : ℕ → ℕ
  | 0 => 0
  | t + 1 => tri t + (t + 1)

/-- `tri' t = t(t-1)/2`. -/
def tri' : ℕ → ℕ
  | 0 => 0
  | t + 1 => tri' t + t

theorem tri_eq (t : ℕ) : 2 * tri t = t * (t + 1) := by
  induction t with
  | zero => rfl
  | succ t ih => simp only [tri]; rw [mul_add, ih]; ring

theorem tri'_eq (t : ℕ) : 2 * tri' t + t = t * t := by
  induction t with
  | zero => rfl
  | succ t ih => simp only [tri']; nlinarith [ih]

theorem le_tri (t : ℕ) : t ≤ tri t := by
  induction t with
  | zero => exact le_rfl
  | succ t ih => simp only [tri]; omega

/-- The term `(-1)^j x^(j(j+1)/2) y^(j(j-1)/2)` of the triple product, `j ∈ ℤ`. -/
def jc (x y : R) : ℤ → R
  | Int.ofNat t => (-1) ^ t * x ^ tri t * y ^ tri' t
  | Int.negSucc t => (-1) ^ (t + 1) * x ^ tri' (t + 1) * y ^ tri (t + 1)

theorem jc_nat (x y : R) (t : ℕ) : jc x y (t : ℤ) = (-1) ^ t * x ^ tri t * y ^ tri' t := rfl

theorem jc_zero (x y : R) : jc x y 0 = 1 := by
  show (-1) ^ 0 * x ^ tri 0 * y ^ tri' 0 = 1
  simp [tri, tri']

theorem jc_negSucc (x y : R) (t : ℕ) :
    jc x y (-(t : ℤ) - 1) = (-1) ^ (t + 1) * x ^ tri' (t + 1) * y ^ tri (t + 1) := by
  rw [show -(t : ℤ) - 1 = Int.negSucc t by rw [Int.negSucc_eq]; ring]; rfl

theorem int_cases (j : ℤ) : ∃ t : ℕ, j = t ∨ j = -(t : ℤ) - 1 := by
  rcases le_or_gt 0 j with h | h
  · exact ⟨j.toNat, Or.inl (by omega)⟩
  · exact ⟨(-j - 1).toNat, Or.inr (by omega)⟩

theorem jc_swap (x y : R) (j : ℤ) : jc x y (-j) = jc y x j := by
  obtain ⟨t, rfl | rfl⟩ := int_cases j
  · rcases t with _ | s
    · simp [jc_zero]
    · rw [show -((s + 1 : ℕ) : ℤ) = -(s : ℤ) - 1 by push_cast; ring, jc_negSucc, jc_nat]; ring
  · rw [show -(-(t : ℤ) - 1) = ((t + 1 : ℕ) : ℤ) by push_cast; ring, jc_nat, jc_negSucc]; ring

theorem jc_succ (x y : R) (n : ℕ) (j : ℤ) (h1 : -(n : ℤ) ≤ j) (h2 : j ≤ n) :
    jc x y (j + 1) * (x * y) ^ ((n : ℤ) - j).toNat = -x * (x * y) ^ n * jc x y j := by
  obtain ⟨t, rfl | rfl⟩ := int_cases j
  · rw [show (t : ℤ) + 1 = ((t + 1 : ℕ) : ℤ) by push_cast; ring, jc_nat, jc_nat,
      show ((n : ℤ) - t).toNat = n - t by omega]
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le (show t ≤ n by omega)
    rw [Nat.add_sub_cancel_left]
    simp only [tri, tri', pow_add, pow_succ, mul_pow]
    ring
  · rcases t with _ | s
    · rw [show -((0 : ℕ) : ℤ) - 1 + 1 = ((0 : ℕ) : ℤ) by omega, jc_nat, jc_negSucc,
        show ((n : ℤ) - (-((0 : ℕ) : ℤ) - 1)).toNat = n + 1 by omega]
      simp only [tri, tri', pow_succ]
      ring
    · rw [show -((s + 1 : ℕ) : ℤ) - 1 + 1 = -(s : ℤ) - 1 by push_cast; ring, jc_negSucc,
        jc_negSucc, show ((n : ℤ) - (-((s + 1 : ℕ) : ℤ) - 1)).toNat = n + (s + 2) by push_cast; omega]
      simp only [tri, tri', pow_add, pow_succ, mul_pow]
      ring

theorem jc_pred (x y : R) (n : ℕ) (j : ℤ) (h1 : -(n : ℤ) ≤ j) (h2 : j ≤ n) :
    jc x y (j - 1) * (x * y) ^ ((n : ℤ) + j).toNat = -y * (x * y) ^ n * jc x y j := by
  have h := jc_succ y x n (-j) (by omega) (by omega)
  rw [show -j + 1 = -(j - 1) by ring, jc_swap y x, jc_swap y x, mul_comm y x,
    show (n : ℤ) - -j = n + j by ring] at h
  exact h

theorem finite_of_bound (f : ℤ → R) (B : ℤ) (h : ∀ j, f j ≠ 0 → -B ≤ j ∧ j ≤ B) :
    (Function.support f).Finite :=
  (Set.finite_Icc (-B) B).subset (fun j hj => h j hj)

/-- **Finite Jacobi triple product.** For `Q = x y`,
`∏_{i<n} (1 - x Q^i)(1 - y Q^i) = Σ_j (-1)^j x^(j(j+1)/2) y^(j(j-1)/2) [2n, n+j]_Q`. -/
theorem jtp_finite (x y : R) (n : ℕ) :
    ∏ i ∈ range n, ((1 - x * (x * y) ^ i) * (1 - y * (x * y) ^ i)) =
      ∑ᶠ j : ℤ, jc x y j * gauss (x * y) (2 * n) ((n : ℤ) + j) := by
  set Q := x * y with hQ
  induction n with
  | zero =>
    rw [prod_range_zero, finsum_eq_single _ 0]
    · simp [gauss, jc_zero]
    · intro j hj; simp [gauss, hj]
  | succ n ih =>
    rw [prod_range_succ, ih]
    set g := fun j : ℤ => jc x y j * gauss Q (2 * n) ((n : ℤ) + j) with hg
    have hgf : (Function.support g).Finite := finite_of_bound g (n + 1) (fun j hj => by
      have := gauss_ne_of_mul Q _ _ _ hj; omega)
    -- the three pieces of `gauss_two_step`
    set p1 := fun j : ℤ => jc x y j * Q ^ ((n : ℤ) + 1 - j).toNat *
      gauss Q (2 * n) ((n : ℤ) + j - 1) with hp1
    set p2 := fun j : ℤ => (1 + Q ^ (2 * n + 1)) * g j with hp2
    set p3 := fun j : ℤ => jc x y j * Q ^ ((n : ℤ) + 1 + j).toNat *
      gauss Q (2 * n) ((n : ℤ) + j + 1) with hp3
    have hf1 : (Function.support p1).Finite := finite_of_bound p1 (n + 2) (fun j hj => by
      have := gauss_ne_of_mul Q _ _ _ hj; omega)
    have hf2 : (Function.support p2).Finite :=
      hgf.subset (Function.support_mul_subset_right _ _)
    have hf3 : (Function.support p3).Finite := finite_of_bound p3 (n + 2) (fun j hj => by
      have := gauss_ne_of_mul Q _ _ _ hj; omega)
    have hsplit : (fun j : ℤ => jc x y j * gauss Q (2 * (n + 1)) (((n + 1 : ℕ) : ℤ) + j)) =
        fun j => p1 j + p2 j + p3 j := by
      funext j
      rw [show 2 * (n + 1) = 2 * n + 2 by ring, gauss_two_step]
      simp only [hp1, hp2, hp3, hg]
      rw [show ((n + 1 : ℕ) : ℤ) + j - 2 = (n : ℤ) + j - 1 by push_cast; ring,
        show ((n + 1 : ℕ) : ℤ) + j - 1 = (n : ℤ) + j by push_cast; ring,
        show ((2 * n : ℕ) : ℤ) + 2 - (((n + 1 : ℕ) : ℤ) + j) = (n : ℤ) + 1 - j by push_cast; ring,
        show ((n + 1 : ℕ) : ℤ) + j = (n : ℤ) + 1 + j by push_cast; ring,
        show (n : ℤ) + 1 + j = (n : ℤ) + j + 1 by ring]
      ring
    -- shift the first and third pieces
    have h1 : ∑ᶠ j, p1 j = -x * Q ^ n * ∑ᶠ j, g j := by
      rw [← finsum_comp_equiv (Equiv.addRight (1 : ℤ)), mul_finsum' _ _ hgf]
      apply finsum_congr; intro j
      simp only [Equiv.coe_addRight, hp1, hg]
      rw [show (n : ℤ) + (j + 1) - 1 = (n : ℤ) + j by ring,
        show (n : ℤ) + 1 - (j + 1) = (n : ℤ) - j by ring]
      by_cases hj : -(n : ℤ) ≤ j ∧ j ≤ n
      · have e := jc_succ x y n j hj.1 hj.2
        rw [← hQ] at e
        rw [e]; ring
      · rw [gauss_eq_zero Q _ _ (by omega)]; ring
    have h3 : ∑ᶠ j, p3 j = -y * Q ^ n * ∑ᶠ j, g j := by
      rw [← finsum_comp_equiv (Equiv.subRight (1 : ℤ)), mul_finsum' _ _ hgf]
      apply finsum_congr; intro j
      simp only [Equiv.subRight_apply, hp3, hg]
      rw [show (n : ℤ) + (j - 1) + 1 = (n : ℤ) + j by ring,
        show (n : ℤ) + 1 + (j - 1) = (n : ℤ) + j by ring]
      by_cases hj : -(n : ℤ) ≤ j ∧ j ≤ n
      · have e := jc_pred x y n j hj.1 hj.2
        rw [← hQ] at e
        rw [e]; ring
      · rw [gauss_eq_zero Q _ _ (by omega)]; ring
    have h2 : ∑ᶠ j, p2 j = (1 + Q ^ (2 * n + 1)) * ∑ᶠ j, g j := by
      rw [mul_finsum' _ _ hgf]
    rw [hsplit, finsum_add_distrib (hf1.union hf2 |>.subset (Function.support_add _ _)) hf3,
      finsum_add_distrib hf1 hf2, h1, h2, h3, hQ]
    ring

/-- A finite sum over `ℤ` as a sum over `t < M` of the terms at `t` and `-t-1`. -/
theorem finsum_int_range {M : Type*} [AddCommMonoid M] (f : ℤ → M) (B : ℕ)
    (h : ∀ j, f j ≠ 0 → -(B : ℤ) ≤ j ∧ j < B) :
    ∑ᶠ j, f j = ∑ t ∈ range B, (f t + f (-(t : ℤ) - 1)) := by
  rw [finsum_eq_sum_of_support_subset f (s := Finset.Ico (-(B : ℤ)) B)
    (by intro j hj; simpa [mem_Ico] using h j hj)]
  have hinj : Function.Injective (fun t : ℕ => -(t : ℤ) - 1) := by intro a b hab; simp at hab; omega
  have hs : Finset.Ico (-(B : ℤ)) B =
      (range B).map Nat.castEmbedding ∪ (range B).map ⟨fun t : ℕ => -(t : ℤ) - 1, hinj⟩ := by
    ext j
    simp only [mem_Ico, mem_union, mem_map, mem_range, Nat.castEmbedding_apply,
      Function.Embedding.coeFn_mk]
    constructor
    · rintro ⟨h1, h2⟩
      rcases le_or_gt 0 j with h0 | h0
      · exact Or.inl ⟨j.toNat, by omega, by omega⟩
      · exact Or.inr ⟨(-j - 1).toNat, by omega, by omega⟩
    · rintro (⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩) <;> omega
  have hd : Disjoint ((range B).map Nat.castEmbedding)
      ((range B).map ⟨fun t : ℕ => -(t : ℤ) - 1, hinj⟩) := by
    rw [Finset.disjoint_left]
    intro j h1 h2
    simp only [mem_map, mem_range, Nat.castEmbedding_apply, Function.Embedding.coeFn_mk] at h1 h2
    obtain ⟨a, _, rfl⟩ := h1
    obtain ⟨b, _, hb⟩ := h2
    omega
  rw [hs, sum_union hd, sum_map, sum_map, sum_add_distrib]
  rfl

end Finite

/-! ## Truncation mod `X^N` and the infinite product -/

section Series

variable {R : Type*} [CommRing R]

/-- Reduction mod `X^N`. -/
noncomputable abbrev modX (N : ℕ) : R⟦X⟧ →+* R⟦X⟧ ⧸ Ideal.span {(X : R⟦X⟧) ^ N} :=
  Ideal.Quotient.mk _

theorem modX_X_pow (N e : ℕ) (h : N ≤ e) : modX N (X ^ e : R⟦X⟧) = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr (pow_dvd_pow X h))

theorem coeff_eq_of_modX (N : ℕ) {f g : R⟦X⟧} (h : modX N f = modX N g) (k : ℕ) (hk : k < N) :
    coeff k f = coeff k g := by
  have h1 := Ideal.Quotient.eq.mp h
  rw [Ideal.mem_span_singleton] at h1
  have h2 := (PowerSeries.X_pow_dvd_iff.mp h1) k hk
  rwa [map_sub, sub_eq_zero] at h2

theorem modX_one_sub (N e : ℕ) (h : N ≤ e) : modX N (1 - X ^ e : R⟦X⟧) = 1 := by
  rw [map_sub, map_one, modX_X_pow N e h, sub_zero]

theorem modX_prod_eq_one {s : Finset ℕ} {F : ℕ → R⟦X⟧} (N : ℕ) (h : ∀ i ∈ s, modX N (F i) = 1) :
    modX N (∏ i ∈ s, F i) = 1 := by
  rw [map_prod]; exact prod_eq_one h

theorem prod_modX_stable (F : ℕ → R⟦X⟧) (N n : ℕ) (hn : N ≤ n)
    (hF : ∀ i, N ≤ i → modX N (F i) = 1) :
    modX N (∏ i ∈ range n, F i) = modX N (∏ i ∈ range N, F i) := by
  rw [← prod_range_mul_prod_Ico F hn, map_mul,
    modX_prod_eq_one N (fun i hi => hF i (mem_Ico.mp hi).1), mul_one]

/-- The `i`-th factor `(1 - q^(m(i+1))) (1 - q^(mi+a)) (1 - q^(mi+b))`, `m = a + b`. -/
noncomputable def jtpFactor (a b i : ℕ) : R⟦X⟧ :=
  (1 - X ^ ((a + b) * (i + 1))) * (1 - X ^ ((a + b) * i + a)) * (1 - X ^ ((a + b) * i + b))

theorem modX_jtpFactor (a b N i : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hi : N ≤ i) :
    modX N (jtpFactor a b i : R⟦X⟧) = 1 := by
  simp only [jtpFactor, map_mul]
  rw [modX_one_sub N ((a + b) * (i + 1)) (by nlinarith), modX_one_sub N ((a + b) * i + a)
    (by nlinarith), modX_one_sub N ((a + b) * i + b) (by nlinarith)]
  ring

/-- Partial sum `Σ_{-n ≤ j < n}` of `(-1)^j q^(a j(j+1)/2 + b j(j-1)/2)`. -/
noncomputable def jtpPartial (a b n : ℕ) : R⟦X⟧ :=
  ∑ t ∈ range n, (jc (X ^ a) (X ^ b) t + jc (X ^ a) (X ^ b) (-(t : ℤ) - 1))

/-- `Σ_{j ∈ ℤ} (-1)^j q^(a j(j+1)/2 + b j(j-1)/2)` (see `coeff_jtpSeries`). -/
noncomputable def jtpSeries (a b : ℕ) : R⟦X⟧ :=
  PowerSeries.mk fun k => coeff k (jtpPartial a b (k + 1) : R⟦X⟧)

theorem modX_jc (a b N : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (j : ℤ) (hj : (N : ℤ) ≤ |j|) :
    modX N (jc (X ^ a) (X ^ b) j : R⟦X⟧) = 0 := by
  obtain ⟨t, rfl | rfl⟩ := int_cases j
  · have hN : N ≤ t := by rcases abs_cases (t : ℤ) with ⟨h1, _⟩ | ⟨h1, _⟩ <;> omega
    have := le_tri t
    rw [jc_nat, ← pow_mul, ← pow_mul]
    simp only [map_mul]
    rw [modX_X_pow N (a * tri t) (by nlinarith)]
    ring
  · have hN : N ≤ t + 1 := by rcases abs_cases (-(t : ℤ) - 1) with ⟨h1, _⟩ | ⟨h1, _⟩ <;> omega
    have := le_tri (t + 1)
    rw [jc_negSucc, ← pow_mul, ← pow_mul]
    simp only [map_mul]
    rw [modX_X_pow N (b * tri (t + 1)) (by nlinarith)]
    ring

theorem modX_one_sub_Q (a b N e : ℕ) (hab : 1 ≤ a + b) (h : N ≤ e) :
    modX N (1 - (X ^ a * X ^ b) ^ e : R⟦X⟧) = 1 := by
  rw [show ((X : R⟦X⟧) ^ a * X ^ b) ^ e = X ^ ((a + b) * e) by ring]
  exact modX_one_sub N _ (by nlinarith)

/-- **Truncated triple product**: modulo `X^N`,
`∏_{i<N} jtpFactor a b i ≡ Σ_{-N ≤ j < N} (-1)^j q^(a j(j+1)/2 + b j(j-1)/2)`. -/
theorem jtp_mod (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (N : ℕ) :
    modX N (∏ i ∈ range N, jtpFactor a b i : R⟦X⟧) = modX N (jtpPartial a b N : R⟦X⟧) := by
  have hfac : ∀ i, (jtpFactor a b i : R⟦X⟧) = (1 - (X ^ a * X ^ b) ^ (i + 1)) *
      ((1 - X ^ a * (X ^ a * X ^ b) ^ i) * (1 - X ^ b * (X ^ a * X ^ b) ^ i)) := by
    intro i; simp only [jtpFactor]; ring
  rw [← prod_modX_stable (jtpFactor a b) N (2 * N) (by omega)
    (fun i hi => modX_jtpFactor a b N i ha hb hi), prod_congr rfl (fun i _ => hfac i),
    prod_mul_distrib, jtp_finite]
  set U := ∏ i ∈ range (2 * N), (1 - ((X : R⟦X⟧) ^ a * X ^ b) ^ (i + 1)) with hU
  -- each term: `U * jc j * [4N, 2N + j]` is `jc j` mod `X^N`
  have key : ∀ j : ℤ, modX N (U * (jc (X ^ a) (X ^ b) j *
      gauss (X ^ a * X ^ b) (2 * (2 * N)) (((2 * N : ℕ) : ℤ) + j))) =
      modX N (jc (X ^ a) (X ^ b) j : R⟦X⟧) := by
    intro j
    by_cases hj : (N : ℤ) ≤ |j|
    · rw [map_mul, map_mul, modX_jc a b N ha hb j hj]; ring
    · have hj' : -(N : ℤ) < j ∧ j < N := by
        constructor <;> rcases abs_cases j with ⟨h1, _⟩ | ⟨h1, _⟩ <;> omega
      set K := (((2 * N : ℕ) : ℤ) + j).toNat with hK
      rw [show ((2 * N : ℕ) : ℤ) + j = (K : ℤ) by omega]
      have hp := gauss_mul_poch (X ^ a * X ^ b : R⟦X⟧) (2 * (2 * N)) K (by omega)
      have hstab : ∀ i, N ≤ i → modX N (1 - ((X : R⟦X⟧) ^ a * X ^ b) ^ (i + 1)) = 1 :=
        fun i hi => modX_one_sub_Q a b N (i + 1) (by omega) (by omega)
      have hUK : modX N U = modX N (∏ i ∈ range K, (1 - ((X : R⟦X⟧) ^ a * X ^ b) ^ (i + 1))) := by
        rw [hU, prod_modX_stable _ N (2 * N) (by omega) hstab,
          prod_modX_stable _ N K (by omega) hstab]
      have hone : modX N (gauss (X ^ a * X ^ b : R⟦X⟧) (2 * (2 * N)) K * U) = 1 := by
        rw [map_mul, hUK, ← map_mul, hp]
        exact modX_prod_eq_one N (fun i _ => modX_one_sub_Q a b N _ (by omega) (by omega))
      rw [map_mul, map_mul, mul_comm, mul_assoc, ← map_mul, hone, mul_one]
  rw [finsum_int_range _ (2 * N + 1) (fun j hj => by
    have := gauss_ne_of_mul _ _ _ _ hj; push_cast at this; omega)]
  rw [mul_sum, map_sum]
  simp only [mul_add, map_add, key]
  rw [jtpPartial, map_sum, ← sum_range_add_sum_Ico _ (show N ≤ 2 * N + 1 by omega)]
  rw [sum_eq_zero (s := Ico N (2 * N + 1)) (fun t ht => by
    have ht' := (mem_Ico.mp ht).1
    rw [modX_jc a b N ha hb _ (by rw [abs_of_nonneg (by positivity)]; exact_mod_cast ht'),
      modX_jc a b N ha hb _ (by rcases abs_cases (-(t : ℤ) - 1) with ⟨h1, _⟩ | ⟨h1, _⟩ <;> omega)]
    ring), add_zero]
  simp only [map_add]

/-- For `k < n`, the coefficient of `q^k` in `∏_{i<n} jtpFactor a b i` is that of
`jtpSeries a b`. -/
theorem jtp_coeff (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (k n : ℕ) (hk : k < n) :
    coeff k (∏ i ∈ range n, jtpFactor a b i : R⟦X⟧) = coeff k (jtpSeries a b : R⟦X⟧) := by
  have h1 := prod_modX_stable (jtpFactor a b : ℕ → R⟦X⟧) (k + 1) n hk
    (fun i hi => modX_jtpFactor a b (k + 1) i ha hb hi)
  rw [coeff_eq_of_modX (k + 1) (h1.trans (jtp_mod a b ha hb (k + 1))) k (by omega), jtpSeries,
    coeff_mk]

theorem coeff_jc_nat (a b k t : ℕ) :
    coeff k (jc (X ^ a) (X ^ b) t : R⟦X⟧) =
      if k = a * tri t + b * tri' t then (-1) ^ t else 0 := by
  rw [jc_nat, ← pow_mul, ← pow_mul, mul_assoc, ← pow_add]
  rcases Nat.even_or_odd t with h | h
  · rw [h.neg_one_pow, h.neg_one_pow, one_mul, coeff_X_pow]
  · rw [h.neg_one_pow, h.neg_one_pow, neg_one_mul, map_neg, coeff_X_pow]
    split_ifs <;> simp

theorem coeff_jc_neg (a b k t : ℕ) :
    coeff k (jc (X ^ a) (X ^ b) (-(t : ℤ) - 1) : R⟦X⟧) =
      if k = a * tri' (t + 1) + b * tri (t + 1) then (-1) ^ (t + 1) else 0 := by
  rw [jc_negSucc, ← pow_mul, ← pow_mul, mul_assoc, ← pow_add]
  rcases Nat.even_or_odd (t + 1) with h | h
  · rw [h.neg_one_pow, h.neg_one_pow, one_mul, coeff_X_pow]
  · rw [h.neg_one_pow, h.neg_one_pow, neg_one_mul, map_neg, coeff_X_pow]
    split_ifs <;> simp

/-- The coefficients of `jtpSeries a b`: `j = t ≥ 0` contributes at `a t(t+1)/2 + b t(t-1)/2`,
`j = -(t+1)` at `a t(t+1)/2 + b (t+1)(t+2)/2`. -/
theorem coeff_jtpSeries (a b k : ℕ) :
    coeff k (jtpSeries a b : R⟦X⟧) = ∑ t ∈ range (k + 1),
      ((if k = a * tri t + b * tri' t then (-1) ^ t else 0) +
        (if k = a * tri' (t + 1) + b * tri (t + 1) then (-1) ^ (t + 1) else 0)) := by
  rw [jtpSeries, coeff_mk, jtpPartial, map_sum]
  exact sum_congr rfl (fun t _ => by rw [map_add, coeff_jc_nat, coeff_jc_neg])

open scoped PowerSeries.WithPiTopology in
/-- A product of factors `F i ≡ 1 mod X^(i+1)` converges (coefficientwise) to `g` once the
truncated products have the coefficients of `g`. -/
theorem hasProd_of_modX [TopologicalSpace R] {F : ℕ → R⟦X⟧} {g : R⟦X⟧}
    (hF : ∀ N i, N ≤ i → modX N (F i) = 1)
    (hg : ∀ k, coeff k (∏ i ∈ range (k + 1), F i) = coeff k g) : HasProd F g := by
  rw [HasProd, WithPiTopology.tendsto_iff_coeff_tendsto]
  intro k
  refine tendsto_atTop_of_eventually_const (fun s (hs : s ≥ range (k + 1)) => ?_)
  rw [← prod_sdiff hs, ← hg k]
  apply coeff_eq_of_modX (k + 1) _ k (by omega)
  rw [map_mul, modX_prod_eq_one (k + 1) (fun i hi => hF _ i ?_), one_mul]
  simp only [mem_sdiff, mem_range] at hi
  omega

open scoped PowerSeries.WithPiTopology in
/-- **Jacobi triple product** (`a, b ≥ 1`, `m = a + b`), coefficientwise in `R⟦X⟧`:
`∏_{i ≥ 0} (1 - q^(m(i+1))) (1 - q^(mi+a)) (1 - q^(mi+b)) =
Σ_{j ∈ ℤ} (-1)^j q^(a j(j+1)/2 + b j(j-1)/2)`. -/
theorem jacobi_triple_product [TopologicalSpace R] (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    HasProd (jtpFactor a b : ℕ → R⟦X⟧) (jtpSeries a b) :=
  hasProd_of_modX (fun N i hi => modX_jtpFactor a b N i ha hb hi)
    (fun k => jtp_coeff a b ha hb k (k + 1) (by omega))

end Series

/-! ## Order-convergent sums -/

section OSum

variable {R : Type*} [CommRing R]

theorem modX_eq_of_coeff (N : ℕ) {f g : R⟦X⟧} (h : ∀ k < N, coeff k f = coeff k g) :
    modX N f = modX N g := by
  apply Ideal.Quotient.eq.mpr
  rw [Ideal.mem_span_singleton, PowerSeries.X_pow_dvd_iff]
  intro k hk
  rw [map_sub, h k hk, sub_self]

theorem eq_of_modX {f g : R⟦X⟧} (h : ∀ N, modX N f = modX N g) : f = g := by
  ext k
  exact coeff_eq_of_modX (k + 1) (h (k + 1)) k (by omega)

/-- `Σ_k f k`, coefficientwise; meaningful when `f k` has order `≥ k`. -/
noncomputable def osum (f : ℕ → R⟦X⟧) : R⟦X⟧ :=
  PowerSeries.mk fun n => coeff n (∑ k ∈ range (n + 1), f k)

/-- Truncating an order-convergent sum. -/
theorem modX_osum (f : ℕ → R⟦X⟧) (hf : ∀ M k, M ≤ k → modX M (f k) = 0) (M : ℕ) :
    modX M (osum f) = modX M (∑ k ∈ range M, f k) := by
  apply modX_eq_of_coeff
  intro n hn
  rw [osum, coeff_mk]
  apply coeff_eq_of_modX (n + 1) _ n (by omega)
  rw [← sum_range_add_sum_Ico _ (show n + 1 ≤ M by omega), map_add, map_sum (modX (n + 1)) _ (Ico _ _),
    sum_eq_zero (fun k hk => hf _ k (mem_Ico.mp hk).1), add_zero]

theorem modX_X_pow_mul (M r : ℕ) (f : R⟦X⟧) (h : modX (M - r) f = 0) :
    modX M (X ^ r * f) = 0 := by
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at h ⊢
  exact (pow_dvd_pow X (show M ≤ r + (M - r) by omega)).trans
    (by rw [pow_add]; exact mul_dvd_mul_left _ h)

theorem modX_neg_X_pow_mul (M r : ℕ) (f : R⟦X⟧) (h : modX (M - r) f = 0) :
    modX M ((-X) ^ r * f) = 0 := by
  rw [neg_pow, mul_assoc, map_mul, modX_X_pow_mul M r f h, mul_zero]

end OSum

/-! ## A conjugate Bailey pair: the q-Gauss sum for `a = q, ρ₁ = q, ρ₂ = -1`

Bailey's lemma with `a = q`, `ρ₁ = q`, `ρ₂ = -1` needs, for every `r`,
`Σ_{k ≥ 0} s_{r,k} = 1/(-q;q)_{r+1}` with
`s_{r,k} = (-q^r;q)_k (-q)^k (q;q)_{k+r} / ((q;q)_k (q;q)_{2r+k+1})` (an instance of the
q-Gauss sum). It is proved here by telescoping: Gosper's certificate for `r = 0`
(`s_{0,K} = R_K - R_{K+1}`, `R_K = s_{0,K} (1 - q^(K+1))/(1+q)`) and a Zeilberger certificate in `r`
(`(1 + q^(r+2)) s_{r+1,K} - s_{r,K} = c_{r,K+1} - c_{r,K}`). The rational identities are
checked in any field (`gosper_field`, `zeil_field`) and transferred to `ℤ⟦X⟧` through its
fraction field. -/

section Field

variable {F : Type*} [Field F]

/-- `(q;q)_m` in a field. -/
def qpF (x : F) (m : ℕ) : F := ∏ i ∈ range m, (1 - x ^ (i + 1))
/-- `(-q^r;q)_k` in a field. -/
def ppF (x : F) (r k : ℕ) : F := ∏ i ∈ range k, (1 + x ^ (r + i))

noncomputable def sF (x : F) (r k : ℕ) : F :=
  ppF x r k * (-x) ^ k * qpF x (k + r) / (qpF x k * qpF x (2 * r + k + 1))

noncomputable def cF (x : F) (r K : ℕ) : F :=
  sF x r K * (-x ^ r) * (x ^ (K + 2 * r + 2) + x ^ (K + r + 1) + x - 1) * (1 - x ^ K) /
    ((1 + x ^ r) * (1 - x ^ (K + 2 * r + 2)))

theorem qpF_succ (x : F) (m : ℕ) : qpF x (m + 1) = qpF x m * (1 - x ^ (m + 1)) :=
  prod_range_succ _ _

theorem ppF_succ (x : F) (r k : ℕ) : ppF x r (k + 1) = ppF x r k * (1 + x ^ (r + k)) :=
  prod_range_succ _ _

theorem ppF_shift (x : F) (r k : ℕ) : ppF x r (k + 1) = (1 + x ^ r) * ppF x (r + 1) k := by
  unfold ppF; rw [prod_range_succ', add_zero, mul_comm]
  congr 1; apply prod_congr rfl; intro i _; ring_nf

theorem zeil_field (x : F) (hx : ∀ i, 1 ≤ i → 1 - x ^ i ≠ 0) (hx' : ∀ i, 1 + x ^ i ≠ 0)
    (r K : ℕ) :
    (1 + x ^ (r + 2)) * sF x (r + 1) K - sF x r K = cF x r (K + 1) - cF x r K := by
  have hq : ∀ m, qpF x m ≠ 0 := fun m => prod_ne_zero_iff.mpr (fun i _ => hx _ (by omega))
  have ps : ppF x (r + 1) K = ppF x r K * (1 + x ^ (r + K)) / (1 + x ^ r) := by
    rw [eq_div_iff (hx' r), mul_comm, ← ppF_shift, ppF_succ]
  unfold cF sF
  rw [ps, ppF_succ, show K + 1 + r = (K + r) + 1 by ring, show K + (r + 1) = (K + r) + 1 by ring,
    show 2 * (r + 1) + K + 1 = (2 * r + K + 1) + 1 + 1 by ring,
    show 2 * r + (K + 1) + 1 = (2 * r + K + 1) + 1 by ring, qpF_succ x (K + r),
    qpF_succ x (2 * r + K + 1 + 1), qpF_succ x (2 * r + K + 1), qpF_succ x K]
  have h1 := hx (K + 1) (by omega)
  have h2 := hx (2 * r + K + 1 + 1) (by omega)
  have h3 := hx (2 * r + K + 1 + 1 + 1) (by omega)
  have h4 := hx (K + 2 * r + 2) (by omega)
  have h5 := hx (K + 1 + 2 * r + 2) (by omega)
  have h6 := hx' r
  have h7 := hq K
  have h8 := hq (2 * r + K + 1)
  field_simp
  ring

theorem gosper_field (x : F) (hx : ∀ i, 1 ≤ i → 1 - x ^ i ≠ 0) (hx' : ∀ i, 1 + x ^ i ≠ 0)
    (K : ℕ) :
    sF x 0 K = sF x 0 K * (1 - x ^ (K + 1)) / (1 + x) -
      sF x 0 (K + 1) * (1 - x ^ (K + 1 + 1)) / (1 + x) := by
  have hq : ∀ m, qpF x m ≠ 0 := fun m => prod_ne_zero_iff.mpr (fun i _ => hx _ (by omega))
  unfold sF
  simp only [mul_zero, zero_add, add_zero]
  rw [ppF_succ, qpF_succ x (K + 1), qpF_succ x K]
  have h1 := hx (K + 1) (by omega)
  have h2 := hx (K + 1 + 1) (by omega)
  have h6 : 1 + x ≠ 0 := by simpa using hx' 1
  have h7 := hq K
  field_simp
  ring

end Field

section Gauss2

open PowerSeries

/-- `1/u` for a power series with constant coefficient 1. -/
noncomputable abbrev inv1 (u : ℤ⟦X⟧) : ℤ⟦X⟧ := PowerSeries.invOfUnit u 1

theorem mul_inv1 (u : ℤ⟦X⟧) (h : constantCoeff u = 1) : u * inv1 u = 1 :=
  PowerSeries.mul_invOfUnit u 1 (by rw [h]; rfl)

/-- `(q;q)_m`. -/
noncomputable def qpS (m : ℕ) : ℤ⟦X⟧ := ∏ i ∈ range m, (1 - X ^ (i + 1))
/-- `(-q^r;q)_k`. -/
noncomputable def ppS (r k : ℕ) : ℤ⟦X⟧ := ∏ i ∈ range k, (1 + X ^ (r + i))

theorem cc_qpS (m : ℕ) : constantCoeff (qpS m) = 1 := by
  unfold qpS; rw [map_prod]; exact prod_eq_one (fun i _ => by simp)

/-- `s_{r,k}` in `ℤ⟦X⟧`. -/
noncomputable def sS (r k : ℕ) : ℤ⟦X⟧ :=
  ppS r k * (-X) ^ k * qpS (k + r) * inv1 (qpS k * qpS (2 * r + k + 1))

/-- `c_{r,K+1}` (the factor `1 + q^r` of `(-q^r;q)_(K+1)` cancelled). -/
noncomputable def cS (r K : ℕ) : ℤ⟦X⟧ :=
  ppS (r + 1) K * (-X) ^ (K + 1) * qpS (K + 1 + r) * (-X ^ r) *
    (X ^ (K + 1 + 2 * r + 2) + X ^ (K + 1 + r + 1) + X - 1) *
    inv1 (qpS K * qpS (2 * r + K + 1 + 2))

/-- Gosper's `R_K`. -/
noncomputable def gS (K : ℕ) : ℤ⟦X⟧ := sS 0 K * (1 - X ^ (K + 1)) * inv1 (1 + X)

/-- The fraction field of `ℤ⟦X⟧`, where the rational identities are checked. -/
abbrev KF := FractionRing ℤ⟦X⟧

noncomputable abbrev φ : ℤ⟦X⟧ →+* KF := algebraMap ℤ⟦X⟧ KF

theorem φ_inj : Function.Injective φ := IsFractionRing.injective ℤ⟦X⟧ KF

theorem φ_inv1 (u : ℤ⟦X⟧) (h : constantCoeff u = 1) : φ (inv1 u) = (φ u)⁻¹ := by
  apply eq_inv_of_mul_eq_one_right
  rw [← map_mul, mul_inv1 u h, map_one]

theorem φ_ne (u : ℤ⟦X⟧) (h : constantCoeff u ≠ 0) : φ u ≠ 0 := by
  intro h0
  apply h
  rw [show u = 0 from φ_inj (by rw [h0, map_zero]), map_zero]

theorem hxK : ∀ i, 1 ≤ i → 1 - (φ X) ^ i ≠ 0 := by
  intro i hi
  rw [← map_pow, ← map_one φ, ← map_sub]
  apply φ_ne
  simp [zero_pow (show i ≠ 0 by omega)]

theorem hxK' : ∀ i, 1 + (φ X) ^ i ≠ 0 := by
  intro i
  rw [← map_pow, ← map_one φ, ← map_add]
  apply φ_ne
  rcases i with _ | i <;> simp

theorem φ_qpS (m : ℕ) : φ (qpS m) = qpF (φ X) m := by
  unfold qpS qpF; simp [map_prod]

theorem φ_ppS (r k : ℕ) : φ (ppS r k) = ppF (φ X) r k := by
  unfold ppS ppF; simp [map_prod]

theorem cc_mul_qpS (a b : ℕ) : constantCoeff (qpS a * qpS b) = 1 := by
  rw [map_mul, cc_qpS, cc_qpS, one_mul]

theorem φ_sS (r k : ℕ) : φ (sS r k) = sF (φ X) r k := by
  unfold sS sF
  rw [map_mul, φ_inv1 _ (cc_mul_qpS _ _)]
  simp only [map_mul, map_pow, map_neg, φ_ppS, φ_qpS]
  rw [div_eq_mul_inv]

theorem φ_cS (r K : ℕ) : φ (cS r K) = cF (φ X) r (K + 1) := by
  have hq : ∀ m, qpF (φ X) m ≠ 0 :=
    fun m => prod_ne_zero_iff.mpr (fun i _ => hxK _ (by omega))
  unfold cS cF sF
  rw [map_mul, φ_inv1 _ (cc_mul_qpS _ _)]
  simp only [map_mul, map_pow, map_neg, map_add, map_sub, map_one, φ_ppS, φ_qpS]
  rw [ppF_shift, qpF_succ (φ X) K, show 2 * r + K + 1 + 2 = (2 * r + (K + 1) + 1) + 1 by ring,
    qpF_succ (φ X) (2 * r + (K + 1) + 1)]
  have h1 := hxK (K + 1) (by omega)
  have h2 := hxK (2 * r + (K + 1) + 1 + 1) (by omega)
  have h3 := hxK (K + 1 + 2 * r + 2) (by omega)
  have h4 := hxK' r
  have h5 := hq K
  have h6 := hq (2 * r + (K + 1) + 1)
  field_simp
  ring

theorem φ_gS (K : ℕ) : φ (gS K) = sF (φ X) 0 K * (1 - φ X ^ (K + 1)) / (1 + φ X) := by
  unfold gS
  rw [map_mul, φ_inv1 _ (by simp), map_mul, φ_sS, map_sub, map_one, map_pow, map_add, map_one,
    div_eq_mul_inv]

/-- Partial sums, `r = 0` (Gosper). -/
theorem sum_sS_zero (M : ℕ) : ∑ k ∈ range M, sS 0 k = gS 0 - gS M := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [sum_range_succ, ih]
    have h := gosper_field (φ X) hxK hxK' M
    have e : sS 0 M = gS M - gS (M + 1) := by
      apply φ_inj
      rw [map_sub, φ_gS, φ_gS, φ_sS]
      exact h
    rw [e]; ring

/-- Partial sums, `r → r + 1` (Zeilberger). -/
theorem sum_sS_succ (r M : ℕ) :
    (1 + X ^ (r + 2)) * ∑ k ∈ range M, sS (r + 1) k - ∑ k ∈ range M, sS r k =
      if M = 0 then 0 else cS r (M - 1) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [sum_range_succ, sum_range_succ]
    have h := zeil_field (φ X) hxK hxK' r M
    have e : (1 + X ^ (r + 2)) * sS (r + 1) M - sS r M =
        cS r M - (if M = 0 then 0 else cS r (M - 1)) := by
      apply φ_inj
      rw [map_sub, map_sub, map_mul, map_add, map_one, map_pow, φ_sS, φ_sS, φ_cS, h]
      rcases M with _ | M
      · simp only [↓reduceIte, map_zero]
        unfold cF
        simp
      · simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel, φ_cS]
    simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
    linear_combination ih + e

theorem modX_sS (M r k : ℕ) (hk : M ≤ k) : modX M (sS r k) = 0 := by
  unfold sS
  rw [mul_comm (ppS r k), mul_assoc, mul_assoc, modX_neg_X_pow_mul M k _ (by
    rw [show M - k = 0 by omega]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (by simp))]

theorem modX_cS (M r K : ℕ) (hK : M ≤ K + 1) : modX M (cS r K) = 0 := by
  unfold cS
  rw [mul_comm (ppS (r + 1) K)]
  simp only [mul_assoc]
  rw [modX_neg_X_pow_mul M (K + 1) _ (by
    rw [show M - (K + 1) = 0 by omega]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (by simp))]

theorem modX_gS (M K : ℕ) (hK : M ≤ K) : modX M (gS K) = 0 := by
  unfold gS
  rw [map_mul, map_mul, modX_sS M 0 K hK, zero_mul, zero_mul]

/-- `G_r = Σ_{k ≥ 0} s_{r,k}`. -/
noncomputable def qGaussSum (r : ℕ) : ℤ⟦X⟧ := osum (sS r)

theorem modX_qGaussSum (r M : ℕ) : modX M (qGaussSum r) = modX M (∑ k ∈ range M, sS r k) :=
  modX_osum _ (fun M k hk => modX_sS M r k hk) M

/-- **q-Gauss sum for the conjugate Bailey pair** (`a = q, ρ₁ = q, ρ₂ = -1`):
`(-q;q)_{r+1} Σ_{k ≥ 0} (-q^r;q)_k (-q)^k (q;q)_{k+r} / ((q;q)_k (q;q)_{2r+k+1}) = 1`. -/
theorem qGaussSum_mul (r : ℕ) : ppS 1 (r + 1) * qGaussSum r = 1 := by
  induction r with
  | zero =>
    have hg : ppS 1 (0 + 1) * gS 0 = 1 := by
      apply φ_inj
      rw [map_mul, φ_gS, φ_ppS, map_one]
      have h1 := hxK 1 le_rfl
      have h2 := hxK' 1
      simp only [pow_one] at h1 h2
      simp only [sF, ppF, qpF, mul_zero, zero_add, range_one, prod_singleton, range_zero,
        prod_empty, pow_zero, mul_one, add_zero, pow_one, one_mul]
      field_simp
    apply eq_of_modX
    intro M
    rw [map_mul, modX_qGaussSum, sum_sS_zero, map_sub, modX_gS M M le_rfl, sub_zero, ← map_mul, hg]
  | succ r ih =>
    apply eq_of_modX
    intro M
    have hrec := sum_sS_succ r M
    have hc : modX M (if M = 0 then 0 else cS r (M - 1)) = 0 := by
      split_ifs with h
      · exact map_zero _
      · exact modX_cS M r (M - 1) (by omega)
    have hpp : ppS 1 (r + 1 + 1) = ppS 1 (r + 1) * (1 + X ^ (r + 2)) := by
      unfold ppS; rw [prod_range_succ]; ring_nf
    have h1 : modX M ((1 + X ^ (r + 2)) * qGaussSum (r + 1)) = modX M (qGaussSum r) := by
      rw [map_mul, modX_qGaussSum, modX_qGaussSum, ← map_mul, ← sub_eq_zero, ← map_sub, hrec]
      exact hc
    rw [hpp, mul_assoc, map_mul, h1, ← map_mul, ih]

end Gauss2

end OpenProblemsLib.QSeries
