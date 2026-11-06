import Mathlib

/-
OEIS A007669 (dead, "Duplicate of A034343"; former name "Number of
orthogonal lattices in dimension n"), offset 1.  A034343: number of
inequivalent binary linear codes of length n and any dimension k <= n
containing no column of zeros.
Conjecture (V. Kotesovec, 2010, in the entry until 2017):
A007669(n) = A178717(n-1) - 1, where A178717(k) is given by Kotesovec's
explicit formula d(k) = 2k + 1 + Σ_{j=1}^{k-1} Σ_{i=F(k-j)+1}^{F(k-j+1)} 2 j φ(i)
(k > 1, F = Fibonacci).  The conjecture is false.

Definitions.
* `V n = Fin n → ZMod 2`; `Code n`: submodules W of V n with no zero
  coordinate (for every i some w ∈ W has w i ≠ 0).
* Equivalence: W ~ W' iff W' is the image of W under a permutation of the
  coordinates (`permL σ`); for GF(2) monomial equivalence is permutation
  equivalence.  `codeSetoid n` (an equivalence relation, proved).
* `a n = Nat.card (Quotient (codeSetoid n))` (A034343 = A007669).
* `A178717 k`: Kotesovec's formula above (the entry's data are its values).

Main theorems.
* `card_code_le`: Nat.card (Code n) ≤ n! * a n (each class is the image of
  the symmetric group).
* `card_code_20`: 1023^10 ≤ Nat.card (Code 20) (graphs {(x, A x)} of 10 x 10
  matrices A over GF(2) with no zero row are distinct codes without zero
  column).
* `a_20_ge`: 515978636151 ≤ a 20, while `A178717_19_le`: A178717 19 ≤ 39 + 18·4181·38·4181.
* `A007669_conj_false`: a 20 ≠ A178717 19 - 1.

Not checked in this file: that `a` is the OEIS sequence beyond the reading
above (dead entry identified with A034343); that Kotesovec's formula equals
A178717's definition (degree of a GF denominator for queens), which the entry
states as an explicit formula; the first failure a(8) = 194 ≠ 196 = A178717(7) - 1
(certificate/burnside.py, Burnside count over all subspaces of GF(2)^8).
-/

namespace A007669

open Finset

abbrev V (n : ℕ) := Fin n → ZMod 2

/-- Permutation of coordinates, f ↦ f ∘ σ. -/
def permL {n : ℕ} (σ : Equiv.Perm (Fin n)) : V n →ₗ[ZMod 2] V n where
  toFun f := f ∘ σ
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem map_permL_one {n : ℕ} (W : Submodule (ZMod 2) (V n)) : W.map (permL 1) = W := by
  have : permL (1 : Equiv.Perm (Fin n)) = LinearMap.id := by
    ext f i; rfl
  rw [this, Submodule.map_id]

theorem map_permL_mul {n : ℕ} (W : Submodule (ZMod 2) (V n)) (σ τ : Equiv.Perm (Fin n)) :
    (W.map (permL σ)).map (permL τ) = W.map (permL (σ * τ)) := by
  rw [← Submodule.map_comp]
  congr 1

/-- Codes of length n without zero column. -/
def Code (n : ℕ) := {W : Submodule (ZMod 2) (V n) // ∀ i, ∃ w ∈ W, w i ≠ 0}

def codeSetoid (n : ℕ) : Setoid (Code n) where
  r W W' := ∃ σ : Equiv.Perm (Fin n), W'.1 = W.1.map (permL σ)
  iseqv := by
    refine ⟨fun W => ⟨1, (map_permL_one _).symm⟩, ?_, ?_⟩
    · rintro W W' ⟨σ, h⟩
      refine ⟨σ⁻¹, ?_⟩
      rw [h, map_permL_mul, mul_inv_cancel, map_permL_one]
    · rintro W W' W'' ⟨σ, h⟩ ⟨τ, h'⟩
      exact ⟨σ * τ, by rw [h', h, map_permL_mul]⟩

/-- A034343(n) = A007669(n): number of inequivalent codes without zero column. -/
noncomputable def a (n : ℕ) : ℕ := Nat.card (Quotient (codeSetoid n))

instance (n : ℕ) : Finite (Code n) := by
  have : Finite (Submodule (ZMod 2) (V n)) :=
    Finite.of_injective (fun W : Submodule (ZMod 2) (V n) => (W : Set (V n)))
      SetLike.coe_injective
  unfold Code; infer_instance

theorem perm_code {n : ℕ} (W : Code n) (σ : Equiv.Perm (Fin n)) :
    ∀ i, ∃ w ∈ W.1.map (permL σ), w i ≠ 0 := by
  intro i
  obtain ⟨w, hw, hwi⟩ := W.2 (σ i)
  exact ⟨permL σ w, Submodule.mem_map_of_mem hw, hwi⟩

theorem card_code_le (n : ℕ) : Nat.card (Code n) ≤ n.factorial * a n := by
  classical
  let f : Equiv.Perm (Fin n) × Quotient (codeSetoid n) → Code n :=
    fun p => ⟨(p.2.out).1.map (permL p.1), perm_code _ _⟩
  have hf : Function.Surjective f := by
    intro W
    have h : (codeSetoid n).r (Quotient.mk (codeSetoid n) W).out W :=
      Quotient.exact (Quotient.out_eq _)
    obtain ⟨σ, hσ⟩ := h
    exact ⟨(σ, Quotient.mk _ W), Subtype.ext hσ.symm⟩
  have := Nat.card_le_card_of_surjective f hf
  rw [Nat.card_prod, Nat.card_perm, Nat.card_fin] at this
  exact this

/-- Matrices with no zero row. -/
abbrev Mat := Fin 10 → {v : Fin 10 → ZMod 2 // v ≠ 0}

/-- x ↦ (x, A x). -/
def graphL (A : Mat) : (Fin 10 → ZMod 2) →ₗ[ZMod 2] V 20 where
  toFun x i := if h : i.val < 10 then x ⟨i.val, h⟩
    else ∑ j, (A ⟨i.val - 10, by omega⟩).1 j * x j
  map_add' x y := by
    funext i
    simp only [Pi.add_apply]
    split_ifs
    · rfl
    · simp [mul_add, Finset.sum_add_distrib]
  map_smul' c x := by
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs
    · rfl
    · simp [Finset.mul_sum]; ring_nf
      exact Finset.sum_congr rfl (fun j _ => by ring)

theorem graphL_single (A : Mat) (j : Fin 10) (i : Fin 20) (h : ¬ i.val < 10) :
    graphL A (Pi.single j 1) i = (A ⟨i.val - 10, by omega⟩).1 j := by
  simp [graphL, h, Pi.single_apply]

theorem graphL_single_lt (A : Mat) (j : Fin 10) (i : Fin 20) (h : i.val < 10) :
    graphL A (Pi.single j 1) i = if (⟨i.val, h⟩ : Fin 10) = j then 1 else 0 := by
  simp [graphL, h, Pi.single_apply]

def graphCode (A : Mat) : Code 20 :=
  ⟨LinearMap.range (graphL A), by
    intro i
    by_cases h : i.val < 10
    · refine ⟨graphL A (Pi.single ⟨i.val, h⟩ 1), LinearMap.mem_range_self _ _, ?_⟩
      rw [graphL_single_lt A _ i h]; simp
    · obtain ⟨j, hj⟩ := Function.ne_iff.mp (A ⟨i.val - 10, by omega⟩).2
      refine ⟨graphL A (Pi.single j 1), LinearMap.mem_range_self _ _, ?_⟩
      rw [graphL_single A j i h]; exact hj⟩

theorem graphCode_inj : Function.Injective graphCode := by
  intro A B hAB
  have hR : LinearMap.range (graphL A) = LinearMap.range (graphL B) := congrArg Subtype.val hAB
  funext r
  apply Subtype.ext
  funext j
  have hm : graphL B (Pi.single j 1) ∈ LinearMap.range (graphL A) := by
    rw [hR]; exact LinearMap.mem_range_self _ _
  obtain ⟨x, hx⟩ := hm
  have hxj : x = Pi.single j 1 := by
    funext l
    have := congrFun hx ⟨l.val, by omega⟩
    simp only [graphL, LinearMap.coe_mk, AddHom.coe_mk, show l.val < 10 from l.2,
      dite_true] at this
    simpa [Pi.single_apply] using this
  subst hxj
  have := congrFun hx ⟨r.val + 10, by omega⟩
  rw [graphL_single A j _ (by simp), graphL_single B j _ (by simp)] at this
  simpa using this

theorem card_mat : Nat.card Mat = 1023 ^ 10 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_subtype_compl, Fintype.card_fun]
  simp

theorem card_code_20 : 1023 ^ 10 ≤ Nat.card (Code 20) := by
  rw [← card_mat]
  exact Nat.card_le_card_of_injective graphCode graphCode_inj

theorem a_20_ge : 515978636151 ≤ a 20 := by
  have h1 := card_code_20
  have h2 := card_code_le 20
  have hf : Nat.factorial 20 = 2432902008176640000 := by decide
  rw [hf] at h2
  omega

/-- Kotesovec's explicit formula for A178717 (k > 1); A178717(1) = 3. -/
def A178717 (k : ℕ) : ℕ :=
  if k = 1 then 3 else
  2 * k + 1 + ∑ j ∈ Ico 1 k, ∑ i ∈ Ioc (Nat.fib (k - j)) (Nat.fib (k - j + 1)), 2 * j * Nat.totient i

theorem A178717_19_le : A178717 19 ≤ 39 + 18 * (4181 * (38 * 4181)) := by
  unfold A178717
  simp only [show (19 : ℕ) ≠ 1 by norm_num, ↓reduceIte]
  have hfib : Nat.fib 19 = 4181 := by decide
  apply Nat.add_le_add_left
  calc ∑ j ∈ Ico 1 19, ∑ i ∈ Ioc (Nat.fib (19 - j)) (Nat.fib (19 - j + 1)), 2 * j * Nat.totient i
      ≤ ∑ j ∈ Ico 1 19, 4181 * (38 * 4181) := by
        apply Finset.sum_le_sum
        intro j hj
        rw [Finset.mem_Ico] at hj
        have hF : Nat.fib (19 - j + 1) ≤ 4181 := hfib ▸ Nat.fib_mono (by omega)
        calc _ ≤ (Ioc (Nat.fib (19 - j)) (Nat.fib (19 - j + 1))).card • (38 * 4181) := by
              apply Finset.sum_le_card_nsmul
              intro i hi
              rw [Finset.mem_Ioc] at hi
              have := Nat.totient_le i
              have : 2 * j * Nat.totient i ≤ 38 * i := by nlinarith
              omega
          _ ≤ 4181 * (38 * 4181) := by
              rw [Nat.card_Ioc, smul_eq_mul]
              exact Nat.mul_le_mul_right _ (by omega)
    _ = 18 * (4181 * (38 * 4181)) := by simp

/-- The conjecture A007669(n) = A178717(n-1) - 1 fails at n = 20. -/
theorem A007669_conj_false : a 20 ≠ A178717 19 - 1 := by
  have h1 := a_20_ge
  have h2 := A178717_19_le
  omega
