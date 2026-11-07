import Mathlib

/-!
# Automatic sequences modulo prime powers: Cartier operators on diagonals

Christol, Denef–Lipshitz and Rowland–Yassawi ("Automatic congruences for diagonals of rational
functions", J. Théor. Nombres Bordeaux 27 (2015)): the diagonal `d(n) = [xⁿ tⁿ] F` of a rational
series `F = N / Q^(p^(a-1))` over `ℤ/p^a` is `p`-automatic, because the Cartier operators
`Λ_r : ∑ c_{i,j} xⁱ tʲ ↦ ∑ c_{pi+r, pj+r} xⁱ tʲ` satisfy `d(pn + r) = diag(Λ_r F)(n)` and send
`N / Q^(p^(a-1))` to `Λ_r(N Q^(p^a - p^(a-1))) / Q^(p^(a-1))`: numerators of bounded degree, a
finite state set. This module proves the operator identities over an arbitrary commutative ring
and supplies a computable list model of bivariate polynomials, so that the finitely many state
transitions of a concrete automaton are checked by `decide`.

Definitions.
* `cart p r f` : the Cartier operator `∑ₙ f_{pn+r} Xⁿ` on `R⟦X⟧` (additive).
* `cart2 p r F`, `sig2 p hp F`, `diag F n` : the bivariate (`R⟦X⟧⟦X⟧`, outer variable `x`, inner
  variable `t`) Cartier operator, Frobenius substitution `x ↦ x^p, t ↦ t^p` and diagonal.
* `ps1`, `ps2` : lists of coefficients as power series; `add1`, `mul1`, `add2`, `mul2`,
  `sig1`, `sig2L`, `evens`, `odds`, `trim1`, `trim2` : computable list operations.

Main results.
* `cart_mul_expand` : `Λ_r(f · g(X^p)) = Λ_r(f) · g` (`r < p`); `cart2_mul_sig2` : the same for
  `cart2`/`sig2`; `diag_cart2` : `diag (cart2 p r F) n = diag F (p n + r)`.
* `ry_step` : if `U · U⁻¹ = 1`, `sig2 U = M · U` (for `U = Q^(p^(a-1))`, `M = Q^(p^a - p^(a-1))`
  this is the congruence `Q^(p^a) ≡ Q(x^p, t^p)^(p^(a-1))` mod `p^a`) and the basis series `eᵢ`
  satisfy `M eᵢ = ∑ⱼ cᵢⱼ · sig2 eⱼ`, then
  `cart2 ((∑ᵢ Nᵢ eᵢ) U⁻¹) = (∑ⱼ cart2 (∑ᵢ Nᵢ cᵢⱼ) eⱼ) U⁻¹`.
  With `e = (1)` this is the Rowland–Yassawi step; extra basis series (e.g. lacunary series with
  `(1 - t) (W + W(t²)) = t`) extend it beyond rational functions.
* `automaton_induction` : a finite family of sequences closed under `n ↦ pn + r` whose values at
  `0` satisfy `P` satisfies `P` everywhere.
* List model (`p = 2`): `ps1_mul1`, `ps2_mul2`, `ps2_add2`, `ps1_sig1`, `ps2_sig2L`,
  `ps2_half` (`Λ_r` on lists), `ps1_trim1`, `ps2_trim2`.
-/

namespace OpenProblemsLib.AutomaticMod

open PowerSeries

/-! ## Cartier operators in one variable -/

section Cartier

variable {R : Type*} [CommRing R]

/-- The Cartier operator `cart p r f = ∑ₙ f_{pn+r} Xⁿ`. -/
noncomputable def cart (p r : ℕ) : R⟦X⟧ →+ R⟦X⟧ where
  toFun f := mk fun n => coeff (p * n + r) f
  map_zero' := by ext; simp
  map_add' f g := by ext; simp

@[simp] theorem coeff_cart (p r n : ℕ) (f : R⟦X⟧) :
    coeff n (cart p r f) = coeff (p * n + r) f := by
  simp [cart]

/-- `Λ_r(f · g(X^p)) = Λ_r(f) · g` for `r < p`. -/
theorem cart_mul_expand (p r : ℕ) (hp : p ≠ 0) (hr : r < p) (f g : R⟦X⟧) :
    cart p r (f * expand p hp g) = cart p r f * g := by
  have hp0 : 0 < p := Nat.pos_of_ne_zero hp
  ext n
  rw [coeff_cart, coeff_mul, coeff_mul]
  simp only [coeff_cart, coeff_expand]
  have hinj : ∀ x ∈ Finset.HasAntidiagonal.antidiagonal n, ∀ y ∈ Finset.HasAntidiagonal.antidiagonal n,
      (fun x : ℕ × ℕ => (p * x.1 + r, p * x.2)) x =
        (fun x : ℕ × ℕ => (p * x.1 + r, p * x.2)) y → x = y := by
    intro x _ y _ h
    simp only [Prod.mk.injEq] at h
    have h1 : p * x.1 = p * y.1 := by omega
    exact Prod.ext (Nat.eq_of_mul_eq_mul_left hp0 h1) (Nat.eq_of_mul_eq_mul_left hp0 h.2)
  have hR : ∑ x ∈ Finset.HasAntidiagonal.antidiagonal n, coeff (p * x.1 + r) f * coeff x.2 g
      = ∑ y ∈ (Finset.HasAntidiagonal.antidiagonal n).image (fun x : ℕ × ℕ => (p * x.1 + r, p * x.2)),
          coeff y.1 f * (if p ∣ y.2 then coeff (y.2 / p) g else 0) := by
    rw [Finset.sum_image hinj]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp [Nat.mul_div_cancel_left _ hp0]
  rw [hR]
  symm
  apply Finset.sum_subset
  · intro y hy
    simp only [Finset.mem_image, Finset.HasAntidiagonal.mem_antidiagonal] at hy ⊢
    obtain ⟨x, hx, rfl⟩ := hy
    rw [← hx, Nat.mul_add]
    omega
  · intro y hy hyn
    by_cases hd : p ∣ y.2
    · exfalso
      apply hyn
      obtain ⟨b, hb⟩ := hd
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hy
      have hbn : b ≤ n := by
        by_contra hc
        have h1 : p * (n + 1) ≤ p * b := Nat.mul_le_mul_left p (by omega)
        rw [Nat.mul_add, Nat.mul_one] at h1
        omega
      have h2 : p * (n - b) + p * b = p * n := by
        rw [← Nat.mul_add, Nat.sub_add_cancel hbn]
      refine Finset.mem_image.mpr ⟨(n - b, b), ?_, ?_⟩
      · simp only [Finset.HasAntidiagonal.mem_antidiagonal]
        omega
      · ext
        · simp only
          omega
        · simp only
          omega
    · simp [hd]

end Cartier

/-! ## Two variables: Cartier operator, Frobenius substitution, diagonal -/

section OuterExpand

variable {S : Type*} [CommRing S]

/-- `expand p` as a ring hom (stated over a generic ring so that `S = R⟦X⟧` picks the
power-series algebra instance of `expand`). -/
noncomputable def oexp (p : ℕ) (hp : p ≠ 0) : S⟦X⟧ →+* S⟦X⟧ := (expand p hp).toRingHom

theorem oexp_apply (p : ℕ) (hp : p ≠ 0) (f : S⟦X⟧) : oexp p hp f = expand p hp f := rfl

end OuterExpand

section TwoVar

variable {R : Type*} [CommRing R]

/-- Bivariate Cartier operator on `R⟦X⟧⟦X⟧`: `[xⁱ tʲ] cart2 p r F = [x^(pi+r) t^(pj+r)] F`. -/
noncomputable def cart2 (p r : ℕ) : R⟦X⟧⟦X⟧ →+ R⟦X⟧⟦X⟧ where
  toFun F := mk fun i => cart p r (coeff (p * i + r) F)
  map_zero' := by ext; simp
  map_add' F G := by ext; simp

@[simp] theorem coeff_cart2 (p r i : ℕ) (F : R⟦X⟧⟦X⟧) :
    coeff i (cart2 p r F) = cart p r (coeff (p * i + r) F) := by
  simp [cart2]

/-- Frobenius substitution `x ↦ x^p`, `t ↦ t^p` on `R⟦X⟧⟦X⟧`. -/
noncomputable def sig2 (p : ℕ) (hp : p ≠ 0) : R⟦X⟧⟦X⟧ →+* R⟦X⟧⟦X⟧ :=
  (PowerSeries.map (oexp (S := R) p hp)).comp (oexp (S := R⟦X⟧) p hp)

theorem sig2_eq_expand (p : ℕ) (hp : p ≠ 0) (H : R⟦X⟧⟦X⟧) :
    sig2 p hp H = expand (R := R⟦X⟧) p hp (PowerSeries.map (oexp (S := R) p hp) H) := by
  ext1 i
  simp only [sig2, RingHom.comp_apply, coeff_map, oexp_apply, coeff_expand]
  split_ifs <;> simp

theorem sig2_C (p : ℕ) (hp : p ≠ 0) (a : R⟦X⟧) : sig2 p hp (C a) = C (expand p hp a) := by
  simp [sig2, oexp_apply, expand_C]

theorem sig2_X (p : ℕ) (hp : p ≠ 0) : sig2 p hp (X : R⟦X⟧⟦X⟧) = X ^ p := by
  simp [sig2, oexp_apply, expand_X]

/-- `Λ_r(F · H(x^p, t^p)) = Λ_r(F) · H` for `r < p`. -/
theorem cart2_mul_sig2 (p r : ℕ) (hp : p ≠ 0) (hr : r < p) (F H : R⟦X⟧⟦X⟧) :
    cart2 p r (F * sig2 p hp H) = cart2 p r F * H := by
  rw [sig2_eq_expand]
  ext1 i
  rw [coeff_cart2]
  have h1 := congrArg (coeff i) (cart_mul_expand p r hp hr F
    (PowerSeries.map (oexp (S := R) p hp) H))
  rw [coeff_cart] at h1
  rw [h1, coeff_mul, coeff_mul, map_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [coeff_cart, coeff_map, coeff_cart2, oexp_apply]
  exact cart_mul_expand p r hp hr _ _

/-- The diagonal `n ↦ [xⁿ tⁿ] F`. -/
noncomputable def diag (F : R⟦X⟧⟦X⟧) (n : ℕ) : R := coeff n (coeff n F)

theorem diag_cart2 (p r n : ℕ) (F : R⟦X⟧⟦X⟧) :
    diag (cart2 p r F) n = diag F (p * n + r) := by
  simp [diag]

/-- One Cartier step on states `(∑ᵢ Nᵢ eᵢ) U⁻¹` (Rowland–Yassawi with a Frobenius basis). -/
theorem ry_step {k : ℕ} (p r : ℕ) (hp : p ≠ 0) (hr : r < p) (U Uinv M : R⟦X⟧⟦X⟧)
    (hU : U * Uinv = 1) (hM : sig2 p hp U = M * U)
    (e : Fin k → R⟦X⟧⟦X⟧) (c : Fin k → Fin k → R⟦X⟧⟦X⟧)
    (he : ∀ i, M * e i = ∑ j, c i j * sig2 p hp (e j)) (N : Fin k → R⟦X⟧⟦X⟧) :
    cart2 p r ((∑ i, N i * e i) * Uinv) =
      (∑ j, cart2 p r (∑ i, N i * c i j) * e j) * Uinv := by
  have hsU : sig2 p hp U * sig2 p hp Uinv = 1 := by rw [← map_mul, hU, map_one]
  have hUinv : Uinv = M * sig2 p hp Uinv := by
    calc Uinv = Uinv * (sig2 p hp U * sig2 p hp Uinv) := by rw [hsU, mul_one]
      _ = (U * Uinv) * (M * sig2 p hp Uinv) := by rw [hM]; ring
      _ = M * sig2 p hp Uinv := by rw [hU, one_mul]
  have hexp : (∑ i, N i * e i) * Uinv =
      ∑ j, (∑ i, N i * c i j) * sig2 p hp (e j * Uinv) := by
    calc (∑ i, N i * e i) * Uinv = (∑ i, N i * e i) * (M * sig2 p hp Uinv) := by
          rw [← hUinv]
      _ = ∑ i, N i * (M * e i) * sig2 p hp Uinv := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun i _ => ?_
          ring
      _ = ∑ i, ∑ j, N i * c i j * sig2 p hp (e j * Uinv) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [he, Finset.mul_sum, Finset.sum_mul]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [map_mul]
          ring
      _ = ∑ j, (∑ i, N i * c i j) * sig2 p hp (e j * Uinv) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.sum_mul]
  rw [hexp, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [cart2_mul_sig2 p r hp hr, mul_assoc]

end TwoVar

/-! ## Automaton induction -/

/-- If finitely many sequences `f s` satisfy `f s (pn + r) = f (δ s r) n`, a set `S` of states
is closed under `δ`, and `P (f s 0)` for `s ∈ S`, then `P (f s n)` for all `n` and `s ∈ S`. -/
theorem automaton_induction {σ α : Type*} (p : ℕ) (hp : 2 ≤ p) (f : σ → ℕ → α)
    (δ : σ → ℕ → σ) (hδ : ∀ s n r, r < p → f s (p * n + r) = f (δ s r) n)
    (S : σ → Prop) (hS : ∀ s, S s → ∀ r, r < p → S (δ s r))
    (P : α → Prop) (h0 : ∀ s, S s → P (f s 0)) :
    ∀ n s, S s → P (f s n) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro s hs
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact h0 s hs
    · have hdiv : n = p * (n / p) + n % p := (Nat.div_add_mod n p).symm
      have hmod : n % p < p := Nat.mod_lt _ (by omega)
      rw [hdiv, hδ s (n / p) (n % p) hmod]
      exact ih (n / p) (Nat.div_lt_self hn (by omega)) _ (hS s hs _ hmod)

/-! ## A computable list model of polynomials in one and two variables -/

section Lists

variable {R : Type*} [CommRing R]

/-- `[a₀, a₁, …] ↦ a₀ + a₁ X + …`. -/
noncomputable def ps1 : List R → R⟦X⟧
  | [] => 0
  | a :: l => C a + X * ps1 l

/-- Coefficientwise sum of lists. -/
def add1 : List R → List R → List R
  | [], m => m
  | a :: l, [] => a :: l
  | a :: l, b :: m => (a + b) :: add1 l m

/-- Product of lists as polynomials. -/
def mul1 : List R → List R → List R
  | [], _ => []
  | a :: l, m => add1 (m.map (a * ·)) ((0 : R) :: mul1 l m)

/-- `t ↦ t²` on lists. -/
def sig1 : List R → List R
  | [] => []
  | a :: l => a :: (0 : R) :: sig1 l

theorem ps1_add1 (l m : List R) : ps1 (add1 l m) = ps1 l + ps1 m := by
  induction l generalizing m with
  | nil => simp [add1, ps1]
  | cons a l ih =>
    cases m with
    | nil => simp [add1, ps1]
    | cons b m => simp only [add1, ps1, ih, map_add]; ring

theorem ps1_map_mul (a : R) (m : List R) : ps1 (m.map (a * ·)) = C a * ps1 m := by
  induction m with
  | nil => simp [ps1]
  | cons b m ih => simp only [List.map_cons, ps1, ih, map_mul]; ring

theorem ps1_mul1 (l m : List R) : ps1 (mul1 l m) = ps1 l * ps1 m := by
  induction l with
  | nil => simp [mul1, ps1]
  | cons a l ih => simp only [mul1, ps1_add1, ps1_map_mul, ps1, ih, map_zero]; ring

theorem ps1_sig1 (l : List R) : ps1 (sig1 l) = expand 2 two_ne_zero (ps1 l) := by
  induction l with
  | nil => simp [sig1, ps1]
  | cons a l ih => simp only [sig1, ps1, ih, map_add, map_mul, expand_C, expand_X, map_zero]; ring

/-- `[A₀, A₁, …] ↦ A₀(t) + x A₁(t) + …` (outer variable `x`, inner lists in `t`). -/
noncomputable def ps2 : List (List R) → R⟦X⟧⟦X⟧
  | [] => 0
  | a :: L => C (ps1 a) + X * ps2 L

def add2 : List (List R) → List (List R) → List (List R)
  | [], M => M
  | a :: L, [] => a :: L
  | a :: L, b :: M => add1 a b :: add2 L M

def mul2 : List (List R) → List (List R) → List (List R)
  | [], _ => []
  | a :: L, M => add2 (M.map (mul1 a)) ([] :: mul2 L M)

def sig2L : List (List R) → List (List R)
  | [] => []
  | a :: L => sig1 a :: [] :: sig2L L

theorem ps2_add2 (L M : List (List R)) : ps2 (add2 L M) = ps2 L + ps2 M := by
  induction L generalizing M with
  | nil => simp [add2, ps2]
  | cons a L ih =>
    cases M with
    | nil => simp [add2, ps2]
    | cons b M => simp only [add2, ps2, ih, ps1_add1, map_add]; ring

theorem ps2_map_mul1 (a : List R) (M : List (List R)) :
    ps2 (M.map (mul1 a)) = C (ps1 a) * ps2 M := by
  induction M with
  | nil => simp [ps2]
  | cons b M ih => simp only [List.map_cons, ps2, ih, ps1_mul1, map_mul]; ring

theorem ps2_mul2 (L M : List (List R)) : ps2 (mul2 L M) = ps2 L * ps2 M := by
  induction L with
  | nil => simp [mul2, ps2]
  | cons a L ih =>
    simp only [mul2, ps2_add2, ps2_map_mul1, ps2, ih, ps1, map_zero]; ring

theorem ps2_sig2L (L : List (List R)) : ps2 (sig2L L) = sig2 2 two_ne_zero (ps2 L) := by
  induction L with
  | nil => simp [sig2L, ps2]
  | cons a L ih =>
    simp only [sig2L, ps2, ih, ps1_sig1, map_add, map_mul, sig2_C, sig2_X, ps1, map_zero]
    ring

/-! ### Cartier operators on lists (`p = 2`) -/

def evens {α : Type*} : List α → List α
  | [] => []
  | [a] => [a]
  | a :: _ :: l => a :: evens l

def odds {α : Type*} : List α → List α
  | [] => []
  | [_] => []
  | _ :: b :: l => b :: odds l

/-- `Λ_r` on lists (`r = 0`: even positions, otherwise odd positions). -/
def half {α : Type*} (r : ℕ) (l : List α) : List α := if r = 0 then evens l else odds l

theorem cart0_step {S : Type*} [CommRing S] (a b : S) (f : S⟦X⟧) :
    cart 2 0 (C a + X * (C b + X * f)) = C a + X * cart 2 0 f := by
  ext n
  cases n with
  | zero => rw [coeff_cart]; simp
  | succ n =>
    rw [coeff_cart, show 2 * (n + 1) + 0 = (2 * n + 1) + 1 by ring]
    simp [coeff_succ_X_mul]

theorem cart1_step {S : Type*} [CommRing S] (a b : S) (f : S⟦X⟧) :
    cart 2 1 (C a + X * (C b + X * f)) = C b + X * cart 2 1 f := by
  ext n
  cases n with
  | zero => rw [coeff_cart]; simp
  | succ n =>
    rw [coeff_cart, show 2 * (n + 1) + 1 = (2 * n + 1 + 1) + 1 by ring]
    simp [coeff_succ_X_mul]

theorem cart0_single {S : Type*} [CommRing S] (a : S) : cart 2 0 (C a) = C a := by
  ext n
  cases n with
  | zero => rw [coeff_cart]
  | succ n => rw [coeff_cart, coeff_C, coeff_C]; simp

theorem cart1_single {S : Type*} [CommRing S] (a : S) : cart 2 1 (C a) = 0 := by
  ext n
  rw [coeff_cart, coeff_C]
  simp

theorem ps1_evens (l : List R) : ps1 (evens l) = cart 2 0 (ps1 l) := by
  induction l using evens.induct with
  | case1 => simp [evens, ps1]
  | case2 a => simp only [evens, ps1, mul_zero, add_zero, cart0_single]
  | case3 a b l ih => simp only [evens, ps1, ih, cart0_step]

theorem ps1_odds (l : List R) : ps1 (odds l) = cart 2 1 (ps1 l) := by
  induction l using odds.induct with
  | case1 => simp [odds, ps1]
  | case2 a => simp only [odds, ps1, cart1_single, mul_zero, add_zero]
  | case3 a b l ih => simp only [odds, ps1, ih, cart1_step]

theorem ps1_half (r : ℕ) (hr : r < 2) (l : List R) : ps1 (half r l) = cart 2 r (ps1 l) := by
  rcases (by omega : r = 0 ∨ r = 1) with rfl | rfl
  · simp [half, ps1_evens]
  · simp [half, ps1_odds]

theorem cart2_0_step (a b : R⟦X⟧) (F : R⟦X⟧⟦X⟧) :
    cart2 2 0 (C a + X * (C b + X * F)) = C (cart 2 0 a) + X * cart2 2 0 F := by
  ext1 n
  cases n with
  | zero => rw [coeff_cart2]; simp
  | succ n =>
    rw [coeff_cart2, show 2 * (n + 1) + 0 = (2 * n + 1) + 1 by ring]
    simp [coeff_succ_X_mul]

theorem cart2_1_step (a b : R⟦X⟧) (F : R⟦X⟧⟦X⟧) :
    cart2 2 1 (C a + X * (C b + X * F)) = C (cart 2 1 b) + X * cart2 2 1 F := by
  ext1 n
  cases n with
  | zero => rw [coeff_cart2]; simp
  | succ n =>
    rw [coeff_cart2, show 2 * (n + 1) + 1 = (2 * n + 1 + 1) + 1 by ring]
    simp [coeff_succ_X_mul]

theorem cart2_0_single (a : R⟦X⟧) : cart2 2 0 (C a : R⟦X⟧⟦X⟧) = C (cart 2 0 a) := by
  ext1 n
  cases n with
  | zero => rw [coeff_cart2]; simp
  | succ n =>
    rw [coeff_cart2, coeff_C, coeff_C]
    simp

theorem cart2_1_single (a : R⟦X⟧) : cart2 2 1 (C a : R⟦X⟧⟦X⟧) = 0 := by
  ext1 n
  rw [coeff_cart2, coeff_C]
  simp

/-- `Λ_r` on bivariate lists. -/
def half2 (r : ℕ) (L : List (List R)) : List (List R) := (half r L).map (half r)

theorem ps2_evens (L : List (List R)) : ps2 ((evens L).map evens) = cart2 2 0 (ps2 L) := by
  induction L using evens.induct with
  | case1 => simp [evens, ps2]
  | case2 a =>
    simp only [evens, List.map, ps2, mul_zero, add_zero, cart2_0_single, ps1_evens]
  | case3 a b L ih =>
    simp only [evens, List.map, ps2] at ih ⊢
    rw [cart2_0_step, ← ih, ps1_evens]

theorem ps2_odds (L : List (List R)) : ps2 ((odds L).map odds) = cart2 2 1 (ps2 L) := by
  induction L using odds.induct with
  | case1 => simp [odds, ps2]
  | case2 a => simp only [odds, List.map, ps2, mul_zero, add_zero, cart2_1_single]
  | case3 a b L ih =>
    simp only [odds, List.map, ps2] at ih ⊢
    rw [cart2_1_step, ← ih, ps1_odds]

theorem ps2_half2 (r : ℕ) (hr : r < 2) (L : List (List R)) :
    ps2 (half2 r L) = cart2 2 r (ps2 L) := by
  rcases (by omega : r = 0 ∨ r = 1) with rfl | rfl
  · exact ps2_evens L
  · exact ps2_odds L

/-! ### Normal forms (strip trailing zeros) -/

variable [DecidableEq R]

def cons1 (a : R) (t : List R) : List R := if a = 0 ∧ t = [] then [] else a :: t

def trim1 : List R → List R
  | [] => []
  | a :: l => cons1 a (trim1 l)

def cons2 (a : List R) (t : List (List R)) : List (List R) :=
  if a = [] ∧ t = [] then [] else a :: t

def trim2 : List (List R) → List (List R)
  | [] => []
  | a :: L => cons2 (trim1 a) (trim2 L)

theorem ps1_trim1 (l : List R) : ps1 (trim1 l) = ps1 l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [trim1, cons1]
    split_ifs with h
    · obtain ⟨rfl, h2⟩ := h
      simp only [ps1]
      rw [← ih, h2]
      simp [ps1]
    · rw [ps1, ps1, ih]

theorem ps2_trim2 (L : List (List R)) : ps2 (trim2 L) = ps2 L := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    simp only [trim2, cons2]
    split_ifs with h
    · obtain ⟨h1, h2⟩ := h
      simp only [ps2]
      rw [← ih, h2, ← ps1_trim1 a, h1]
      simp [ps2, ps1]
    · rw [ps2, ps2, ih, ps1_trim1]

end Lists

end OpenProblemsLib.AutomaticMod
