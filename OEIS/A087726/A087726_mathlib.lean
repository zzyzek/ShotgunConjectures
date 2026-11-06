import Mathlib

/-
OEIS A087726 (offset 1): number of matrices X in M_2(Z/nZ) with X^2 = 0.
Conjecture (Ben Branman, 2013): a(n) = n^2 if and only if n is squarefree.

Definitions.  `A087726 n = Nat.card {X : Matrix (Fin 2) (Fin 2) (ZMod n) // X * X = 0}`.

Main theorem.
* `A087726_conj`: for n ≥ 1, A087726 n = n^2 ↔ Squarefree n.
* `A087726_israel`: R. Israel's conjectured formula (2015), for primes p, k ≥ 1:
  4 a(p^k) = (1 + 3p^2 + 2k(p^2-1) + (-1)^k (p^2-1)) p^(2k-2).
Also `A087726_ge` (n^2 ≤ a(n) for n ≥ 1), `A087726_mul` (multiplicative),
`A087726_prime` (a(p) = p^2), `A087726_prime_pow_gt` (p^(2k) < a(p^k), k ≥ 2),
`A087726_rec` (a(p^(m+2)) = p^(2m+2)(p^2-1) + p^4 a(p^m)),
`A087726_prime_pow_closed` (a(p^k) = p^(4⌊k/2⌋) + ⌈k/2⌉ p^(2k-2) (p^2-1)).

Route.
* `A087726_mul`: CRT, ZMod (m n) ≃+* ZMod m × ZMod n applied entrywise.
* `A087726_prime`: over the field ZMod p, X^2 = 0 iff X = !![a, b; c, -a] with
  a^2 + bc = 0; these are `fb a u` (b = u a unit), `fc 0 u` (b = 0, c = u a
  unit) and 0, so p(p-1) + (p-1) + 1 = p^2.
* `A087726_prime_pow_gt`: in ZMod (p^k), k ≥ 2, three disjoint families of
  square-zero matrices: `fb a u` (entry (0,1) a unit), `fc (p t) u` (entry
  (1,0) a unit, entry (0,1) a multiple of p), and `fg`, the matrices with
  entries (0,0), (1,0), (1,1) multiples of p^⌈k/2⌉ and entry (0,1) a multiple of
  p^⌊k/2⌋.  Sizes p^k φ(p^k), p^(k-1) φ(p^k), p^(3⌊k/2⌋+⌈k/2⌉); the sum
  exceeds p^(2k).
* `A087726_conj`: induction over coprime factorisations.

Not checked in this file: agreement with the OEIS data terms
(certificate/check.py counts by brute force for n ≤ 40 and compares with the b-file).
-/

namespace OEIS087726

open Matrix

/-- 2 × 2 matrices over ZMod n. -/
abbrev Mat (n : ℕ) := Matrix (Fin 2) (Fin 2) (ZMod n)

/-- A087726: number of X in M_2(Z/nZ) with X^2 = 0. -/
noncomputable def A087726 (n : ℕ) : ℕ := Nat.card {X : Mat n // X * X = 0}

theorem sq_zero_iff {R : Type*} [CommRing R] (X : Matrix (Fin 2) (Fin 2) R) :
    X * X = 0 ↔ (X 0 0 * X 0 0 + X 0 1 * X 1 0 = 0 ∧ X 0 0 * X 0 1 + X 0 1 * X 1 1 = 0 ∧
      X 1 0 * X 0 0 + X 1 1 * X 1 0 = 0 ∧ X 1 0 * X 0 1 + X 1 1 * X 1 1 = 0) := by
  constructor
  · intro h
    have e : ∀ i j, (X * X) i j = 0 := fun i j => by rw [h]; rfl
    simp only [Matrix.mul_apply, Fin.sum_univ_two] at e
    exact ⟨e 0 0, e 0 1, e 1 0, e 1 1⟩
  · rintro ⟨h1, h2, h3, h4⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, h1, h2, h3, h4]

theorem mat_eq {R : Type*} (X : Matrix (Fin 2) (Fin 2) R) (a b c d : R)
    (h0 : X 0 0 = a) (h1 : X 0 1 = b) (h2 : X 1 0 = c) (h3 : X 1 1 = d) :
    X = !![a, b; c, d] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h0, h1, h2, h3]

/-! ### Multiplicativity -/

theorem A087726_mul {m n : ℕ} (h : m.Coprime n) :
    A087726 (m * n) = A087726 m * A087726 n := by
  let e := ZMod.chineseRemainder h
  let f₁ : ZMod (m * n) →+* ZMod m := (RingHom.fst _ _).comp e.toRingHom
  let f₂ : ZMod (m * n) →+* ZMod n := (RingHom.snd _ _).comp e.toRingHom
  let E : Mat (m * n) ≃ Mat m × Mat n :=
    { toFun := fun X => (f₁.mapMatrix X, f₂.mapMatrix X)
      invFun := fun P => Matrix.of fun i j => e.symm (P.1 i j, P.2 i j)
      left_inv := by
        intro X
        ext i j
        simp [f₁, f₂]
      right_inv := by
        intro P
        ext i j <;> simp [f₁, f₂] }
  have key : ∀ X : Mat (m * n),
      X * X = 0 ↔ ((E X).1 * (E X).1 = 0 ∧ (E X).2 * (E X).2 = 0) := by
    intro X
    simp only [E, Equiv.coe_fn_mk, ← map_mul]
    constructor
    · intro hX
      rw [hX]
      simp
    · rintro ⟨h1, h2⟩
      ext i j
      have a1 := congrFun (congrFun h1 i) j
      have a2 := congrFun (congrFun h2 i) j
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.zero_apply] at a1 a2
      apply e.injective
      show e ((X * X) i j) = e 0
      rw [map_zero]
      exact Prod.ext (by simpa [f₁] using a1) (by simpa [f₂] using a2)
  unfold A087726
  rw [← Nat.card_prod]
  apply Nat.card_congr
  exact (E.subtypeEquiv key).trans
    (Equiv.subtypeProdEquivProd (p := fun A : Mat m => A * A = 0)
      (q := fun B : Mat n => B * B = 0))

/-! ### Two families of trace-zero square-zero matrices -/

/-- !![a, u; -a^2 u⁻¹, -a] with u a unit. -/
def fb {q : ℕ} (a : ZMod q) (u : (ZMod q)ˣ) : Mat q :=
  !![a, (u : ZMod q); -(a ^ 2 * ((u⁻¹ : (ZMod q)ˣ) : ZMod q)), -a]

/-- !![a, -a^2 u⁻¹; u, -a] with u a unit. -/
def fc {q : ℕ} (a : ZMod q) (u : (ZMod q)ˣ) : Mat q :=
  !![a, -(a ^ 2 * ((u⁻¹ : (ZMod q)ˣ) : ZMod q)); (u : ZMod q), -a]

theorem fb_sq {q : ℕ} (a : ZMod q) (u : (ZMod q)ˣ) : fb a u * fb a u = 0 := by
  have hu : (u : ZMod q) * ((u⁻¹ : (ZMod q)ˣ) : ZMod q) = 1 := Units.mul_inv u
  rw [sq_zero_iff]
  simp only [fb, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one]
  refine ⟨?_, ?_, ?_, ?_⟩
  · linear_combination (-a ^ 2) * hu
  · ring
  · ring
  · linear_combination (-a ^ 2) * hu

theorem fc_sq {q : ℕ} (a : ZMod q) (u : (ZMod q)ˣ) : fc a u * fc a u = 0 := by
  have hu : (u : ZMod q) * ((u⁻¹ : (ZMod q)ˣ) : ZMod q) = 1 := Units.mul_inv u
  rw [sq_zero_iff]
  simp only [fc, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one]
  refine ⟨?_, ?_, ?_, ?_⟩
  · linear_combination (-a ^ 2) * hu
  · ring
  · ring
  · linear_combination (-a ^ 2) * hu

theorem fb_inj {q : ℕ} : Function.Injective (fun x : ZMod q × (ZMod q)ˣ => fb x.1 x.2) := by
  rintro ⟨a, u⟩ ⟨a', u'⟩ h
  have h0 := congrFun (congrFun h 0) 0
  have h1 := congrFun (congrFun h 0) 1
  simp [fb] at h0 h1
  simp [h0, Units.ext h1]

theorem fb_01 {q : ℕ} (a : ZMod q) (u : (ZMod q)ˣ) : fb a u 0 1 = u := by simp [fb]
theorem fc_10 {q : ℕ} (a : ZMod q) (u : (ZMod q)ˣ) : fc a u 1 0 = u := by simp [fc]
theorem fc_01 {q : ℕ} (a : ZMod q) (u : (ZMod q)ˣ) :
    fc a u 0 1 = -(a ^ 2 * ((u⁻¹ : (ZMod q)ˣ) : ZMod q)) := by simp [fc]
theorem fc_00 {q : ℕ} (a : ZMod q) (u : (ZMod q)ˣ) : fc a u 0 0 = a := by simp [fc]

theorem card_filter_eq (n : ℕ) [NeZero n] :
    A087726 n = (Finset.univ.filter (fun X : Mat n => X * X = 0)).card := by
  unfold A087726
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

/-! ### Primes -/

theorem A087726_prime (p : ℕ) [hp : Fact p.Prime] : A087726 p = p ^ 2 := by
  have hp2 := hp.out.two_le
  rw [card_filter_eq]
  set FB := (Finset.univ : Finset (ZMod p × (ZMod p)ˣ)).image (fun x => fb x.1 x.2)
  set FC := (Finset.univ : Finset (ZMod p)ˣ).image (fun u => fc 0 u)
  have hFB : FB.card = p * (p - 1) := by
    rw [Finset.card_image_of_injective _ fb_inj, Finset.card_univ, Fintype.card_prod,
      ZMod.card, ZMod.card_units]
  have hFC : FC.card = p - 1 := by
    rw [Finset.card_image_of_injective, Finset.card_univ, ZMod.card_units]
    intro u u' h
    have := congrFun (congrFun h 1) 0
    simp only [fc_10] at this
    exact Units.ext this
  have hd1 : Disjoint FB FC := by
    rw [Finset.disjoint_left]
    rintro X hX hX'
    obtain ⟨⟨a, u⟩, -, rfl⟩ := Finset.mem_image.1 hX
    obtain ⟨u', -, h⟩ := Finset.mem_image.1 hX'
    have := congrFun (congrFun h 0) 1
    rw [fc_01, fb_01, zero_pow two_ne_zero, zero_mul, neg_zero] at this
    exact u.ne_zero this.symm
  have hd2 : Disjoint (FB ∪ FC) {0} := by
    rw [Finset.disjoint_singleton_right, Finset.mem_union, not_or]
    constructor
    · intro hX
      obtain ⟨⟨a, u⟩, -, h⟩ := Finset.mem_image.1 hX
      have := congrFun (congrFun h 0) 1
      rw [fb_01] at this
      exact u.ne_zero this
    · intro hX
      obtain ⟨u, -, h⟩ := Finset.mem_image.1 hX
      have := congrFun (congrFun h 1) 0
      rw [fc_10] at this
      exact u.ne_zero this
  have hS : Finset.univ.filter (fun X : Mat p => X * X = 0) = FB ∪ FC ∪ {0} := by
    apply Finset.Subset.antisymm
    · intro X hX
      rw [Finset.mem_filter] at hX
      obtain ⟨h1, h2, h3, h4⟩ := (sq_zero_iff X).1 hX.2
      simp only [Finset.mem_union, Finset.mem_singleton]
      by_cases hb : X 0 1 = 0
      · rw [hb] at h1 h4
        have ha : X 0 0 = 0 := by simpa using h1
        have hd : X 1 1 = 0 := by simpa using h4
        by_cases hc : X 1 0 = 0
        · right
          ext i j
          fin_cases i <;> fin_cases j <;> simp [ha, hb, hc, hd]
        · left; right
          refine Finset.mem_image.2 ⟨Units.mk0 _ hc, Finset.mem_univ _, ?_⟩
          symm
          apply mat_eq <;> simp [ha, hb, hd]
      · left; left
        have hd : X 1 1 = -X 0 0 := by
          have : X 0 1 * (X 0 0 + X 1 1) = 0 := by linear_combination h2
          rcases mul_eq_zero.1 this with h | h
          · exact absurd h hb
          · linear_combination h
        have hc : X 1 0 = -(X 0 0 ^ 2 * (X 0 1)⁻¹) := by
          field_simp
          linear_combination h1
        refine Finset.mem_image.2 ⟨(X 0 0, Units.mk0 _ hb), Finset.mem_univ _, ?_⟩
        symm
        apply mat_eq <;> simp [hc, hd]
    · intro X hX
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      simp only [Finset.mem_union, Finset.mem_singleton] at hX
      rcases hX with (hX | hX) | rfl
      · obtain ⟨⟨a, u⟩, -, rfl⟩ := Finset.mem_image.1 hX
        exact fb_sq a u
      · obtain ⟨u, -, rfl⟩ := Finset.mem_image.1 hX
        exact fc_sq 0 u
      · simp
  rw [hS, Finset.card_union_of_disjoint hd2, Finset.card_union_of_disjoint hd1, hFB, hFC,
    Finset.card_singleton]
  obtain ⟨s, rfl⟩ : ∃ s, p = s + 1 := ⟨p - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  ring

/-! ### Prime powers p^k, k ≥ 2 -/

section PrimePow

variable (p : ℕ) [hp : Fact p.Prime] (k : ℕ)

omit hp in
theorem P_pow_k : ((p : ZMod (p ^ k))) ^ k = 0 := by
  rw [← Nat.cast_pow]
  exact ZMod.natCast_self _

theorem P_not_unit (hk : 1 ≤ k) (j : ℕ) (hj : 1 ≤ j) (y : ZMod (p ^ k)) :
    ¬ IsUnit ((p : ZMod (p ^ k)) ^ j * y) := by
  intro hu
  have h1 : IsUnit ((p : ZMod (p ^ k)) ^ j) := isUnit_of_mul_isUnit_left hu
  have h2 : IsUnit (p : ZMod (p ^ k)) := (isUnit_pow_iff (by omega)).1 h1
  have h3 : IsUnit ((p : ZMod (p ^ k)) ^ k) := h2.pow k
  rw [P_pow_k] at h3
  have : Fact (1 < p ^ k) := ⟨Nat.one_lt_pow (by omega) hp.out.one_lt⟩
  exact not_isUnit_zero h3

theorem mInj (j : ℕ) (hj : j ≤ k) :
    Function.Injective (fun t : Fin (p ^ (k - j)) => (p : ZMod (p ^ k)) ^ j * ((t : ℕ) : ZMod (p ^ k))) := by
  intro t t' h
  simp only at h
  have h' : ((p ^ j * (t : ℕ) : ℕ) : ZMod (p ^ k)) = ((p ^ j * (t' : ℕ) : ℕ) : ZMod (p ^ k)) := by
    push_cast
    exact h
  rw [ZMod.natCast_eq_natCast_iff'] at h'
  have hp0 : 0 < p ^ j := pow_pos hp.out.pos j
  have hlt : ∀ s : Fin (p ^ (k - j)), p ^ j * (s : ℕ) < p ^ k := fun s => by
    calc p ^ j * (s : ℕ) < p ^ j * p ^ (k - j) := Nat.mul_lt_mul_of_pos_left s.isLt hp0
      _ = p ^ k := by rw [← pow_add]; congr 1; omega
  rw [Nat.mod_eq_of_lt (hlt t), Nat.mod_eq_of_lt (hlt t')] at h'
  exact Fin.ext (Nat.eq_of_mul_eq_mul_left hp0 h')

/-- Matrices with entries (0,0), (1,0), (1,1) multiples of p^hi and (0,1) a multiple of p^lo. -/
def fg (hi lo : ℕ) (t : Fin (p ^ (k - hi)) × Fin (p ^ (k - lo)) × Fin (p ^ (k - hi)) × Fin (p ^ (k - hi))) :
    Mat (p ^ k) :=
  !![(p : ZMod (p ^ k)) ^ hi * ((t.1 : ℕ) : ZMod (p ^ k)),
     (p : ZMod (p ^ k)) ^ lo * ((t.2.1 : ℕ) : ZMod (p ^ k));
     (p : ZMod (p ^ k)) ^ hi * ((t.2.2.1 : ℕ) : ZMod (p ^ k)),
     (p : ZMod (p ^ k)) ^ hi * ((t.2.2.2 : ℕ) : ZMod (p ^ k))]

omit hp in
theorem fg_sq (hi lo : ℕ) (h1 : k ≤ hi + hi) (h2 : k ≤ lo + hi) (t) :
    fg p k hi lo t * fg p k hi lo t = 0 := by
  have e1 : ((p : ZMod (p ^ k))) ^ (hi + hi) = 0 := pow_eq_zero_of_le h1 (P_pow_k p k)
  have e2 : ((p : ZMod (p ^ k))) ^ (lo + hi) = 0 := pow_eq_zero_of_le h2 (P_pow_k p k)
  rw [sq_zero_iff]
  simp only [fg, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one]
  set P := (p : ZMod (p ^ k))
  set a := ((t.1 : ℕ) : ZMod (p ^ k))
  set b := ((t.2.1 : ℕ) : ZMod (p ^ k))
  set c := ((t.2.2.1 : ℕ) : ZMod (p ^ k))
  set d := ((t.2.2.2 : ℕ) : ZMod (p ^ k))
  refine ⟨?_, ?_, ?_, ?_⟩
  · linear_combination (a * a) * e1 + (b * c) * e2
  · linear_combination (a * b + b * d) * e2
  · linear_combination (c * a + d * c) * e1
  · linear_combination (c * b) * e2 + (d * d) * e1

theorem fg_inj (hi lo : ℕ) (h1 : hi ≤ k) (h2 : lo ≤ k) : Function.Injective (fg p k hi lo) := by
  rintro ⟨a, b, c, d⟩ ⟨a', b', c', d'⟩ h
  have e00 := congrFun (congrFun h 0) 0
  have e01 := congrFun (congrFun h 0) 1
  have e10 := congrFun (congrFun h 1) 0
  have e11 := congrFun (congrFun h 1) 1
  simp only [fg, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one] at e00 e01 e10 e11
  rw [mInj p k hi h1 e00, mInj p k lo h2 e01, mInj p k hi h1 e10, mInj p k hi h1 e11]

theorem A087726_prime_pow_gt (hk : 2 ≤ k) : p ^ (2 * k) < A087726 (p ^ k) := by
  have hp2 := hp.out.two_le
  have : NeZero (p ^ k) := ⟨by positivity⟩
  rw [card_filter_eq]
  set hi := (k + 1) / 2
  set lo := k / 2
  have hhi : 1 ≤ hi := by omega
  have hlo : 1 ≤ lo := by omega
  set FB := (Finset.univ : Finset (ZMod (p ^ k) × (ZMod (p ^ k))ˣ)).image (fun x => fb x.1 x.2)
  set FC := (Finset.univ : Finset (Fin (p ^ (k - 1)) × (ZMod (p ^ k))ˣ)).image
    (fun x => fc ((p : ZMod (p ^ k)) ^ 1 * ((x.1 : ℕ) : ZMod (p ^ k))) x.2)
  set G := (Finset.univ : Finset (Fin (p ^ (k - hi)) × Fin (p ^ (k - lo)) × Fin (p ^ (k - hi)) ×
    Fin (p ^ (k - hi)))).image (fg p k hi lo)
  have htot : Fintype.card (ZMod (p ^ k))ˣ = p ^ (k - 1) * (p - 1) := by
    rw [ZMod.card_units_eq_totient, Nat.totient_prime_pow hp.out (by omega)]
  have hFB : FB.card = p ^ k * (p ^ (k - 1) * (p - 1)) := by
    rw [Finset.card_image_of_injective _ fb_inj, Finset.card_univ, Fintype.card_prod,
      ZMod.card, htot]
  have hFC : FC.card = p ^ (k - 1) * (p ^ (k - 1) * (p - 1)) := by
    rw [Finset.card_image_of_injective, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, htot]
    rintro ⟨t, u⟩ ⟨t', u'⟩ h
    have e00 := congrFun (congrFun h 0) 0
    have e10 := congrFun (congrFun h 1) 0
    simp only [fc_00, fc_10] at e00 e10
    rw [mInj p k 1 (by omega) e00, Units.ext e10]
  have hG : G.card = p ^ (k - hi) * (p ^ (k - lo) * (p ^ (k - hi) * p ^ (k - hi))) := by
    rw [Finset.card_image_of_injective _ (fg_inj p k hi lo (by omega) (by omega)), Finset.card_univ]
    simp only [Fintype.card_prod, Fintype.card_fin]
  have hd1 : Disjoint FB FC := by
    rw [Finset.disjoint_left]
    rintro X hX hX'
    obtain ⟨⟨a, u⟩, -, rfl⟩ := Finset.mem_image.1 hX
    obtain ⟨⟨t, u'⟩, -, h⟩ := Finset.mem_image.1 hX'
    have := congrFun (congrFun h 0) 1
    rw [fc_01, fb_01] at this
    apply P_not_unit p k (by omega) 1 le_rfl
      (-((p : ZMod (p ^ k)) * ((t : ℕ) : ZMod (p ^ k)) ^ 2 * ((u'⁻¹ : (ZMod (p ^ k))ˣ) : ZMod (p ^ k))))
    have hu : IsUnit ((u : ZMod (p ^ k))) := u.isUnit
    rw [← this] at hu
    convert hu using 1
    ring
  have hd2 : Disjoint (FB ∪ FC) G := by
    rw [Finset.disjoint_left]
    rintro X hX hX'
    obtain ⟨t, -, rfl⟩ := Finset.mem_image.1 hX'
    rcases Finset.mem_union.1 hX with hX | hX
    · obtain ⟨⟨a, u⟩, -, h⟩ := Finset.mem_image.1 hX
      have := congrFun (congrFun h 0) 1
      rw [fb_01] at this
      have hu : IsUnit ((u : ZMod (p ^ k))) := u.isUnit
      rw [this] at hu
      simp only [fg, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.empty_val', Matrix.cons_val_fin_one] at hu
      exact P_not_unit p k (by omega) lo hlo _ hu
    · obtain ⟨⟨s, u⟩, -, h⟩ := Finset.mem_image.1 hX
      have := congrFun (congrFun h 1) 0
      rw [fc_10] at this
      have hu : IsUnit ((u : ZMod (p ^ k))) := u.isUnit
      rw [this] at hu
      simp only [fg, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.empty_val', Matrix.cons_val_fin_one] at hu
      exact P_not_unit p k (by omega) hi hhi _ hu
  have hsub : FB ∪ FC ∪ G ⊆ Finset.univ.filter (fun X : Mat (p ^ k) => X * X = 0) := by
    intro X hX
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rcases Finset.mem_union.1 hX with hX | hX
    · rcases Finset.mem_union.1 hX with hX | hX
      · obtain ⟨⟨a, u⟩, -, rfl⟩ := Finset.mem_image.1 hX
        exact fb_sq a u
      · obtain ⟨⟨t, u⟩, -, rfl⟩ := Finset.mem_image.1 hX
        exact fc_sq _ u
    · obtain ⟨t, -, rfl⟩ := Finset.mem_image.1 hX
      exact fg_sq p k hi lo (by omega) (by omega) t
  refine lt_of_lt_of_le ?_ (Finset.card_le_card hsub)
  rw [Finset.card_union_of_disjoint hd2, Finset.card_union_of_disjoint hd1, hFB, hFC, hG]
  obtain ⟨r, rfl⟩ : ∃ r, p = r + 1 := ⟨p - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  rcases Nat.even_or_odd k with ⟨m, hm⟩ | ⟨m, hm⟩
  · subst hm
    have e1 : (m + m + 1) / 2 = m := by omega
    have e2 : (m + m) / 2 = m := by omega
    simp only [hi, lo, e1, e2, show m + m - m = m by omega]
    have hpos : 0 < (r + 1) ^ (m + m) * ((r + 1) ^ (m + m - 1) * r) := by
      have : 1 ≤ r := by omega
      positivity
    have : (r + 1) ^ (2 * (m + m)) = (r + 1) ^ m * ((r + 1) ^ m * ((r + 1) ^ m * (r + 1) ^ m)) := by
      rw [← pow_add, ← pow_add, ← pow_add]; congr 1; omega
    omega
  · subst hm
    have e1 : (2 * m + 1 + 1) / 2 = m + 1 := by omega
    have e2 : (2 * m + 1) / 2 = m := by omega
    simp only [hi, lo, e1, e2, show 2 * m + 1 - (m + 1) = m by omega,
      show 2 * m + 1 - m = m + 1 by omega, show 2 * m + 1 - 1 = 2 * m by omega]
    have b1 : (r + 1) ^ (2 * m) = (r + 1) ^ m * (r + 1) ^ m := by rw [← pow_add, two_mul]
    have b2 : (r + 1) ^ (2 * m + 1) = (r + 1) ^ m * (r + 1) ^ m * (r + 1) := by rw [pow_succ, b1]
    have b3 : (r + 1) ^ (m + 1) = (r + 1) ^ m * (r + 1) := pow_succ _ _
    have b4 : (r + 1) ^ (2 * (2 * m + 1)) = ((r + 1) ^ m * (r + 1) ^ m * (r + 1)) ^ 2 := by
      rw [mul_comm 2, pow_mul, b2]
    rw [b4, b2, b1, b3]
    have hX : 0 < (r + 1) ^ m := by positivity
    generalize (r + 1) ^ m = X at hX ⊢
    have : 1 ≤ r := by omega
    have hXX : 0 < X * X * X * X := by positivity
    nlinarith

end PrimePow

/-! ### The conjecture -/

theorem A087726_one : A087726 1 = 1 := by
  unfold A087726
  rw [Nat.card_eq_one_iff_exists]
  refine ⟨⟨0, by simp⟩, fun Y => Subtype.ext ?_⟩
  ext i j
  exact Subsingleton.elim _ _

theorem A087726_main (n : ℕ) (hn : 1 ≤ n) :
    n ^ 2 ≤ A087726 n ∧ (A087726 n = n ^ 2 ↔ Squarefree n) := by
  induction n using Nat.recOnPosPrimePosCoprime with
  | prime_pow p k hp hk =>
    have : Fact p.Prime := ⟨hp⟩
    rcases (show k = 1 ∨ 2 ≤ k by omega) with rfl | hk2
    · rw [pow_one, A087726_prime]
      exact ⟨le_rfl, ⟨fun _ => hp.prime.squarefree, fun _ => rfl⟩⟩
    · have h := A087726_prime_pow_gt p k hk2
      have hsq : ¬ Squarefree (p ^ k) := by
        rw [Nat.squarefree_pow_iff hp.ne_one (by omega)]
        rintro ⟨-, h1⟩
        omega
      rw [← pow_mul, mul_comm k 2]
      exact ⟨h.le, ⟨fun h' => by omega, fun h' => absurd h' hsq⟩⟩
  | zero => omega
  | one =>
    rw [A087726_one]
    simp
  | coprime a b ha hb hab iha ihb =>
    obtain ⟨la, ea⟩ := iha (by omega)
    obtain ⟨lb, eb⟩ := ihb (by omega)
    have ha2 : 0 < a ^ 2 := by positivity
    have hb2 : 0 < b ^ 2 := by positivity
    rw [A087726_mul hab, Nat.squarefree_mul_iff, mul_pow]
    refine ⟨Nat.mul_le_mul la lb, ⟨fun h => ?_, ?_⟩⟩
    · have hx : A087726 a = a ^ 2 := by
        by_contra hne
        have hlt : a ^ 2 + 1 ≤ A087726 a := lt_of_le_of_ne la (Ne.symm hne)
        have := Nat.mul_le_mul hlt lb
        nlinarith
      have hy : A087726 b = b ^ 2 := by
        by_contra hne
        have hlt : b ^ 2 + 1 ≤ A087726 b := lt_of_le_of_ne lb (Ne.symm hne)
        have := Nat.mul_le_mul la hlt
        nlinarith
      exact ⟨hab, ea.1 hx, eb.1 hy⟩
    · rintro ⟨-, sa, sb⟩
      rw [ea.2 sa, eb.2 sb]

/-- n^2 ≤ a(n) for every n ≥ 1. -/
theorem A087726_ge (n : ℕ) (hn : 1 ≤ n) : n ^ 2 ≤ A087726 n := (A087726_main n hn).1

/-- **A087726** (Branman's conjecture): a(n) = n^2 if and only if n is squarefree. -/
theorem A087726_conj (n : ℕ) (hn : 1 ≤ n) : A087726 n = n ^ 2 ↔ Squarefree n :=
  (A087726_main n hn).2

/-! ### Exact count for prime powers (R. Israel's formula) -/

section Exact

variable (p : ℕ) [hp : Fact p.Prime]

/-- A matrix is primitive if some entry is a unit. -/
def Prim {q : ℕ} (X : Mat q) : Prop :=
  IsUnit (X 0 0) ∨ IsUnit (X 0 1) ∨ IsUnit (X 1 0) ∨ IsUnit (X 1 1)

theorem nonunit_iff (k : ℕ) (hk : 1 ≤ k) (x : ZMod (p ^ k)) : IsUnit x ↔ ¬ p ∣ x.val := by
  have : NeZero (p ^ k) := ⟨by have := hp.out.pos; positivity⟩
  conv_lhs => rw [← ZMod.natCast_zmod_val x]
  exact ZMod.isUnit_natCast_iff_not_dvd_pow hp.out (by omega)

/-- Primitive square-zero matrices mod p^k are exactly the families `fb`, `fc (p t)`. -/
theorem prim_sq_mem (k : ℕ) (hk : 1 ≤ k) (X : Mat (p ^ k)) (hX : X * X = 0) (hP : Prim X) :
    (∃ a : ZMod (p ^ k), ∃ u : (ZMod (p ^ k))ˣ, X = fb a u) ∨
    (∃ t : Fin (p ^ (k - 1)), ∃ u : (ZMod (p ^ k))ˣ,
      X = fc ((p : ZMod (p ^ k)) ^ 1 * ((t : ℕ) : ZMod (p ^ k))) u) := by
  have : NeZero (p ^ k) := ⟨by have := hp.out.pos; positivity⟩
  obtain ⟨h1, h2, h3, h4⟩ := (sq_zero_iff X).1 hX
  by_cases hb : IsUnit (X 0 1)
  · left
    set u := hb.unit
    have hu : (u : ZMod (p ^ k)) = X 0 1 := hb.unit_spec
    have had : X 0 0 + X 1 1 = 0 := by
      have : X 0 1 * (X 0 0 + X 1 1) = 0 := by linear_combination h2
      exact (hb.mul_right_eq_zero).1 this
    have hc : X 1 0 = -(X 0 0 ^ 2 * ((u⁻¹ : (ZMod (p ^ k))ˣ) : ZMod (p ^ k))) := by
      have hi : ((u⁻¹ : (ZMod (p ^ k))ˣ) : ZMod (p ^ k)) * X 0 1 = 1 := by rw [← hu]; exact u.inv_mul
      linear_combination ((u⁻¹ : (ZMod (p ^ k))ˣ) : ZMod (p ^ k)) * h1 - (X 1 0) * hi
    refine ⟨X 0 0, u, ?_⟩
    show X = !![X 0 0, (u : ZMod (p ^ k)); -(X 0 0 ^ 2 * ((u⁻¹ : (ZMod (p ^ k))ˣ) : ZMod (p ^ k))), -X 0 0]
    exact mat_eq X _ _ _ _ rfl hu.symm hc (by linear_combination had)
  · by_cases hc : IsUnit (X 1 0)
    · right
      set u := hc.unit
      have hu : (u : ZMod (p ^ k)) = X 1 0 := hc.unit_spec
      have had : X 0 0 + X 1 1 = 0 := by
        have : X 1 0 * (X 0 0 + X 1 1) = 0 := by linear_combination h3
        exact (hc.mul_right_eq_zero).1 this
      have hbv : X 0 1 = -(X 0 0 ^ 2 * ((u⁻¹ : (ZMod (p ^ k))ˣ) : ZMod (p ^ k))) := by
        have hi : ((u⁻¹ : (ZMod (p ^ k))ˣ) : ZMod (p ^ k)) * X 1 0 = 1 := by rw [← hu]; exact u.inv_mul
        linear_combination ((u⁻¹ : (ZMod (p ^ k))ˣ) : ZMod (p ^ k)) * h1 - (X 0 1) * hi
      -- the (0,0) entry is a multiple of p
      have ha : ¬ IsUnit (X 0 0) := by
        intro ha
        have : IsUnit (X 0 0 ^ 2) := ha.pow 2
        rw [show X 0 0 ^ 2 = -(X 0 1 * X 1 0) by linear_combination h1, IsUnit.neg_iff] at this
        exact hb (isUnit_of_mul_isUnit_left this)
      rw [nonunit_iff p k hk, not_not] at ha
      obtain ⟨s, hs⟩ := ha
      have hslt : s < p ^ (k - 1) := by
        have hv := ZMod.val_lt (X 0 0)
        rw [hs] at hv
        have e : p ^ k = p * p ^ (k - 1) := by rw [← pow_succ']; congr 1; omega
        rw [e] at hv
        exact Nat.lt_of_mul_lt_mul_left hv
      have haeq : X 0 0 = (p : ZMod (p ^ k)) ^ 1 * ((s : ℕ) : ZMod (p ^ k)) := by
        rw [← ZMod.natCast_zmod_val (X 0 0), hs]
        push_cast
        ring
      refine ⟨⟨s, hslt⟩, u, ?_⟩
      show X = !![(p : ZMod (p ^ k)) ^ 1 * ((s : ℕ) : ZMod (p ^ k)),
        -(((p : ZMod (p ^ k)) ^ 1 * ((s : ℕ) : ZMod (p ^ k))) ^ 2 * ((u⁻¹ : (ZMod (p ^ k))ˣ) : ZMod (p ^ k)));
        (u : ZMod (p ^ k)), -((p : ZMod (p ^ k)) ^ 1 * ((s : ℕ) : ZMod (p ^ k)))]
      exact mat_eq X _ _ _ _ haeq (by rw [hbv, haeq]) hu.symm (by rw [← haeq]; linear_combination had)
    · exfalso
      have hbc : ¬ IsUnit (X 0 1 * X 1 0) := fun h => hb (isUnit_of_mul_isUnit_left h)
      have hcb : ¬ IsUnit (X 1 0 * X 0 1) := fun h => hc (isUnit_of_mul_isUnit_left h)
      have ha : ¬ IsUnit (X 0 0) := by
        intro ha
        have : IsUnit (X 0 0 ^ 2) := ha.pow 2
        rw [show X 0 0 ^ 2 = -(X 0 1 * X 1 0) by linear_combination h1, IsUnit.neg_iff] at this
        exact hbc this
      have hd : ¬ IsUnit (X 1 1) := by
        intro hd
        have : IsUnit (X 1 1 ^ 2) := hd.pow 2
        rw [show X 1 1 ^ 2 = -(X 1 0 * X 0 1) by linear_combination h4, IsUnit.neg_iff] at this
        exact hcb this
      rcases hP with h | h | h | h
      · exact ha h
      · exact hb h
      · exact hc h
      · exact hd h

/-- Lift (w, t) ↦ p·w + p^(m+1)·t from ZMod (p^m) × Fin p to ZMod (p^(m+2)). -/
def psi (m : ℕ) (w : ZMod (p ^ m)) (t : Fin p) : ZMod (p ^ (m + 2)) :=
  ((p * w.val + p ^ (m + 1) * (t : ℕ) : ℕ) : ZMod (p ^ (m + 2)))

theorem psi_lt (m : ℕ) (w : ZMod (p ^ m)) (t : Fin p) :
    p * w.val + p ^ (m + 1) * (t : ℕ) < p ^ (m + 2) := by
  have : NeZero (p ^ m) := ⟨by have := hp.out.pos; positivity⟩
  have hw := ZMod.val_lt w
  have ht := t.isLt
  have e1 : p ^ (m + 1) = p * p ^ m := by ring
  have e2 : p ^ (m + 2) = p * (p ^ m * p) := by ring
  rw [e1, e2, mul_assoc, ← mul_add]
  apply Nat.mul_lt_mul_of_pos_left _ hp.out.pos
  calc w.val + p ^ m * (t : ℕ) < p ^ m + p ^ m * (t : ℕ) := by omega
    _ = p ^ m * ((t : ℕ) + 1) := by ring
    _ ≤ p ^ m * p := Nat.mul_le_mul_left _ ht

theorem psi_inj (m : ℕ) {w w' : ZMod (p ^ m)} {t t' : Fin p} (h : psi p m w t = psi p m w' t') :
    w = w' ∧ t = t' := by
  have : NeZero (p ^ m) := ⟨by have := hp.out.pos; positivity⟩
  unfold psi at h
  rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt (psi_lt p m w t),
    Nat.mod_eq_of_lt (psi_lt p m w' t')] at h
  have e1 : p ^ (m + 1) = p * p ^ m := by ring
  rw [e1, mul_assoc, mul_assoc, ← mul_add, ← mul_add] at h
  have h' := Nat.eq_of_mul_eq_mul_left hp.out.pos h
  have hP : 0 < p ^ m := by have := hp.out.pos; positivity
  have hm1 : (w.val + p ^ m * t) % p ^ m = (w'.val + p ^ m * t') % p ^ m := by rw [h']
  rw [Nat.add_mul_mod_self_left, Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt (ZMod.val_lt w), Nat.mod_eq_of_lt (ZMod.val_lt w')] at hm1
  have hd1 : (w.val + p ^ m * t) / p ^ m = (w'.val + p ^ m * t') / p ^ m := by rw [h']
  rw [Nat.add_mul_div_left _ _ hP, Nat.add_mul_div_left _ _ hP,
    Nat.div_eq_of_lt (ZMod.val_lt w), Nat.div_eq_of_lt (ZMod.val_lt w')] at hd1
  exact ⟨ZMod.val_injective _ hm1, Fin.ext (by simpa using hd1)⟩

theorem psi_not_unit (m : ℕ) (w : ZMod (p ^ m)) (t : Fin p) : ¬ IsUnit (psi p m w t) := by
  rw [nonunit_iff p (m + 2) (by omega), not_not]
  unfold psi
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt (psi_lt p m w t)]
  exact Dvd.dvd.add (dvd_mul_right _ _) (Dvd.dvd.mul_right (dvd_pow_self _ (by omega)) _)

theorem psi_surj (m : ℕ) (x : ZMod (p ^ (m + 2))) (hx : ¬ IsUnit x) :
    ∃ w t, psi p m w t = x := by
  have : NeZero (p ^ (m + 2)) := ⟨by have := hp.out.pos; positivity⟩
  have : NeZero (p ^ m) := ⟨by have := hp.out.pos; positivity⟩
  rw [nonunit_iff p (m + 2) (by omega), not_not] at hx
  obtain ⟨q, hq⟩ := hx
  have hP : 0 < p ^ m := by have := hp.out.pos; positivity
  have hqlt : q < p ^ m * p := by
    have hv := ZMod.val_lt x
    rw [hq, show p ^ (m + 2) = p * (p ^ m * p) by ring] at hv
    exact Nat.lt_of_mul_lt_mul_left hv
  refine ⟨((q % p ^ m : ℕ) : ZMod (p ^ m)), ⟨q / p ^ m, (Nat.div_lt_iff_lt_mul hP).2 (by linarith)⟩, ?_⟩
  unfold psi
  rw [ZMod.val_natCast, Nat.mod_mod, ← ZMod.natCast_zmod_val x, hq]
  congr 1
  simp only
  have := Nat.mod_add_div q (p ^ m)
  calc p * (q % p ^ m) + p ^ (m + 1) * (q / p ^ m) = p * (q % p ^ m + p ^ m * (q / p ^ m)) := by ring
    _ = p * q := by rw [this]

/-- The lifted matrix p·W + p^(m+1)·T. -/
def Psi (m : ℕ) (W : Mat (p ^ m)) (T : Fin 2 → Fin 2 → Fin p) : Mat (p ^ (m + 2)) :=
  Matrix.of fun i j => psi p m (W i j) (T i j)

theorem Psi_sq_iff (m : ℕ) (W : Mat (p ^ m)) (T : Fin 2 → Fin 2 → Fin p) :
    Psi p m W T * Psi p m W T = 0 ↔ W * W = 0 := by
  have : NeZero (p ^ m) := ⟨by have := hp.out.pos; positivity⟩
  have e1 : ((p : ZMod (p ^ (m + 2)))) ^ (m + 2) = 0 := P_pow_k p (m + 2)
  have e2 : ((p : ZMod (p ^ (m + 2)))) ^ (2 * m + 2) = 0 :=
    pow_eq_zero_of_le (by omega) e1
  let N : Fin 2 → Fin 2 → ℕ := fun i j =>
    (W i 0).val * (W 0 j).val + (W i 1).val * (W 1 j).val
  have hX : ∀ i j, (Psi p m W T * Psi p m W T) i j = ((p ^ 2 * N i j : ℕ) : ZMod (p ^ (m + 2))) := by
    intro i j
    simp only [Psi, psi, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, N]
    push_cast
    set P := (p : ZMod (p ^ (m + 2)))
    set a := (((W i 0).val : ℕ) : ZMod (p ^ (m + 2)))
    set b := (((W 0 j).val : ℕ) : ZMod (p ^ (m + 2)))
    set c := (((W i 1).val : ℕ) : ZMod (p ^ (m + 2)))
    set d := (((W 1 j).val : ℕ) : ZMod (p ^ (m + 2)))
    set ta := (((T i 0 : ℕ) : ℕ) : ZMod (p ^ (m + 2)))
    set tb := (((T 0 j : ℕ) : ℕ) : ZMod (p ^ (m + 2)))
    set tc := (((T i 1 : ℕ) : ℕ) : ZMod (p ^ (m + 2)))
    set td := (((T 1 j : ℕ) : ℕ) : ZMod (p ^ (m + 2)))
    linear_combination (a * tb + ta * b + c * td + tc * d) * e1 + (ta * tb + tc * td) * e2
  have hW : ∀ i j, (W * W) i j = ((N i j : ℕ) : ZMod (p ^ m)) := by
    intro i j
    simp only [Matrix.mul_apply, Fin.sum_univ_two, N]
    push_cast
    simp only [ZMod.natCast_zmod_val]
  have hdv : ∀ n : ℕ, p ^ (m + 2) ∣ p ^ 2 * n ↔ p ^ m ∣ n := by
    intro n
    rw [show p ^ (m + 2) = p ^ 2 * p ^ m by ring]
    exact Nat.mul_dvd_mul_iff_left (by have := hp.out.pos; positivity)
  rw [← Matrix.ext_iff, ← Matrix.ext_iff]
  simp only [Matrix.zero_apply, hX, hW, ZMod.natCast_eq_zero_iff, hdv]

theorem Psi_inj (m : ℕ) : Function.Injective (fun x : Mat (p ^ m) × (Fin 2 → Fin 2 → Fin p) =>
    Psi p m x.1 x.2) := by
  rintro ⟨W, T⟩ ⟨W', T'⟩ h
  have hij : ∀ i j, W i j = W' i j ∧ T i j = T' i j := fun i j =>
    psi_inj p m (by simpa [Psi] using congrFun (congrFun h i) j)
  simp only [Prod.mk.injEq]
  exact ⟨Matrix.ext fun i j => (hij i j).1, funext fun i => funext fun j => (hij i j).2⟩

/-- Recursion: a(p^(m+2)) = p^(2m+2) (p^2 - 1) + p^4 a(p^m). -/
theorem A087726_rec (m : ℕ) :
    A087726 (p ^ (m + 2)) = p ^ (m + 2) * (p ^ (m + 1) * (p - 1)) + p ^ (m + 1) * (p ^ (m + 1) * (p - 1))
      + A087726 (p ^ m) * p ^ 4 := by
  classical
  have : NeZero (p ^ (m + 2)) := ⟨by have := hp.out.pos; positivity⟩
  have : NeZero (p ^ m) := ⟨by have := hp.out.pos; positivity⟩
  set k := m + 2 with hkdef
  rw [card_filter_eq, card_filter_eq]
  set S := Finset.univ.filter (fun X : Mat (p ^ k) => X * X = 0)
  rw [← Finset.card_filter_add_card_filter_not (s := S) (p := fun X : Mat (p ^ k) => Prim X)]
  -- primitive part
  set FB := (Finset.univ : Finset (ZMod (p ^ k) × (ZMod (p ^ k))ˣ)).image (fun x => fb x.1 x.2)
  set FC := (Finset.univ : Finset (Fin (p ^ (k - 1)) × (ZMod (p ^ k))ˣ)).image
    (fun x => fc ((p : ZMod (p ^ k)) ^ 1 * ((x.1 : ℕ) : ZMod (p ^ k))) x.2)
  have htot : Fintype.card (ZMod (p ^ k))ˣ = p ^ (k - 1) * (p - 1) := by
    rw [ZMod.card_units_eq_totient, Nat.totient_prime_pow hp.out (by omega)]
  have hFB : FB.card = p ^ k * (p ^ (k - 1) * (p - 1)) := by
    rw [Finset.card_image_of_injective _ fb_inj, Finset.card_univ, Fintype.card_prod,
      ZMod.card, htot]
  have hFC : FC.card = p ^ (k - 1) * (p ^ (k - 1) * (p - 1)) := by
    rw [Finset.card_image_of_injective, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, htot]
    rintro ⟨t, u⟩ ⟨t', u'⟩ h
    have e00 := congrFun (congrFun h 0) 0
    have e10 := congrFun (congrFun h 1) 0
    simp only [fc_00, fc_10] at e00 e10
    rw [mInj p k 1 (by omega) e00, Units.ext e10]
  have hd1 : Disjoint FB FC := by
    rw [Finset.disjoint_left]
    rintro X hX hX'
    obtain ⟨⟨a, u⟩, -, rfl⟩ := Finset.mem_image.1 hX
    obtain ⟨⟨t, u'⟩, -, h⟩ := Finset.mem_image.1 hX'
    have := congrFun (congrFun h 0) 1
    rw [fc_01, fb_01] at this
    apply P_not_unit p k (by omega) 1 le_rfl
      (-((p : ZMod (p ^ k)) * ((t : ℕ) : ZMod (p ^ k)) ^ 2 * ((u'⁻¹ : (ZMod (p ^ k))ˣ) : ZMod (p ^ k))))
    have hu : IsUnit ((u : ZMod (p ^ k))) := u.isUnit
    rw [← this] at hu
    convert hu using 1
    ring
  have hprim : S.filter (fun X => Prim X) = FB ∪ FC := by
    apply Finset.Subset.antisymm
    · intro X hX
      rw [Finset.mem_filter, Finset.mem_filter] at hX
      rw [Finset.mem_union]
      rcases prim_sq_mem p k (by omega) X hX.1.2 hX.2 with ⟨a, u, rfl⟩ | ⟨t, u, rfl⟩
      · exact Or.inl (Finset.mem_image.2 ⟨(a, u), Finset.mem_univ _, rfl⟩)
      · exact Or.inr (Finset.mem_image.2 ⟨(t, u), Finset.mem_univ _, rfl⟩)
    · intro X hX
      rw [Finset.mem_filter, Finset.mem_filter]
      rcases Finset.mem_union.1 hX with hX | hX
      · obtain ⟨⟨a, u⟩, -, rfl⟩ := Finset.mem_image.1 hX
        refine ⟨⟨Finset.mem_univ _, fb_sq a u⟩, Or.inr (Or.inl ?_)⟩
        rw [fb_01]; exact u.isUnit
      · obtain ⟨⟨t, u⟩, -, rfl⟩ := Finset.mem_image.1 hX
        refine ⟨⟨Finset.mem_univ _, fc_sq _ u⟩, Or.inr (Or.inr (Or.inl ?_))⟩
        rw [fc_10]; exact u.isUnit
  -- non-primitive part
  have hnon : S.filter (fun X => ¬ Prim X) =
      ((Finset.univ.filter (fun W : Mat (p ^ m) => W * W = 0)) ×ˢ
        (Finset.univ : Finset (Fin 2 → Fin 2 → Fin p))).image (fun x => Psi p m x.1 x.2) := by
    apply Finset.Subset.antisymm
    · intro X hX
      rw [Finset.mem_filter, Finset.mem_filter] at hX
      obtain ⟨⟨-, hsq⟩, hnp⟩ := hX
      have hall : ∀ i j, ¬ IsUnit (X i j) := by
        intro i j hu
        apply hnp
        fin_cases i <;> fin_cases j
        · exact Or.inl hu
        · exact Or.inr (Or.inl hu)
        · exact Or.inr (Or.inr (Or.inl hu))
        · exact Or.inr (Or.inr (Or.inr hu))
      have hex : ∀ i j, ∃ w t, psi p m w t = X i j := fun i j => psi_surj p m (X i j) (hall i j)
      choose W T hWT using hex
      have hXe : Psi p m (Matrix.of W) T = X := by
        ext i j
        exact hWT i j
      refine Finset.mem_image.2 ⟨(Matrix.of W, T), ?_, hXe⟩
      rw [Finset.mem_product, Finset.mem_filter]
      refine ⟨⟨Finset.mem_univ _, ?_⟩, Finset.mem_univ _⟩
      rw [← Psi_sq_iff p m, hXe]
      exact hsq
    · intro X hX
      obtain ⟨⟨W, T⟩, hWT, rfl⟩ := Finset.mem_image.1 hX
      rw [Finset.mem_product, Finset.mem_filter] at hWT
      rw [Finset.mem_filter, Finset.mem_filter]
      refine ⟨⟨Finset.mem_univ _, (Psi_sq_iff p m W T).2 hWT.1.2⟩, ?_⟩
      rintro (h | h | h | h) <;> exact psi_not_unit p m _ _ h
  rw [hprim, hnon, Finset.card_union_of_disjoint hd1, hFB, hFC,
    Finset.card_image_of_injective _ (Psi_inj p m), Finset.card_product, Finset.card_univ]
  simp only [Fintype.card_fun, Fintype.card_fin, hkdef]
  rw [show m + 2 - 1 = m + 1 by omega]
  ring

/-- Closed form: a(p^k) = p^(4⌊k/2⌋) + ⌈k/2⌉ p^(2k-2) (p^2 - 1). -/
theorem A087726_prime_pow_closed (k : ℕ) :
    (A087726 (p ^ k) : ℤ) = (p : ℤ) ^ (4 * (k / 2)) + ((k + 1) / 2 : ℕ) * (p : ℤ) ^ (2 * k - 2) * ((p : ℤ) ^ 2 - 1) := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    match k, ih with
    | 0, _ => simp [A087726_one]
    | 1, _ => simp [A087726_prime]
    | (m + 2), ih =>
      have h := A087726_rec p m
      have hm := ih m (by omega)
      have hp1 : 1 ≤ p := hp.out.pos
      rw [show (m + 2) / 2 = m / 2 + 1 by omega, show (m + 2 + 1) / 2 = (m + 1) / 2 + 1 by omega,
        show 2 * (m + 2) - 2 = 2 * m + 2 by omega, h]
      generalize hc : (m + 1) / 2 = c at hm ⊢
      generalize hd : m / 2 = d at hm ⊢
      push_cast [Nat.cast_sub hp1]
      rw [hm]
      rcases Nat.eq_zero_or_pos m with rfl | hm0
      · norm_num at hc hd
        subst hc hd
        ring
      · obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
        rw [show 2 * (n + 1) - 2 = 2 * n by omega]
        ring

/-- **R. Israel's formula** (A087726, 2015): for primes p and k ≥ 1,
a(p^k) = (1 + 3p^2 + 2k(p^2-1) + (-1)^k (p^2-1)) p^(2k-2) / 4. -/
theorem A087726_israel (k : ℕ) (hk : 1 ≤ k) :
    4 * (A087726 (p ^ k) : ℤ) =
      (1 + 3 * (p : ℤ) ^ 2 + 2 * k * ((p : ℤ) ^ 2 - 1) + (-1) ^ k * ((p : ℤ) ^ 2 - 1)) * (p : ℤ) ^ (2 * k - 2) := by
  rw [A087726_prime_pow_closed]
  rcases Nat.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · rw [show (m + m) / 2 = m by omega, show (m + m + 1) / 2 = m by omega,
      show 2 * (m + m) - 2 = 4 * m - 2 by omega, Even.neg_one_pow ⟨m, rfl⟩]
    have e : (p : ℤ) ^ (4 * m) = (p : ℤ) ^ (4 * m - 2) * (p : ℤ) ^ 2 := by
      rw [← pow_add]; congr 1; omega
    rw [e]
    push_cast
    ring
  · rw [show (2 * m + 1) / 2 = m by omega, show (2 * m + 1 + 1) / 2 = m + 1 by omega,
      show 2 * (2 * m + 1) - 2 = 4 * m by omega, Odd.neg_one_pow ⟨m, rfl⟩]
    push_cast
    ring

end Exact
