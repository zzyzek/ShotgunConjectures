/-
OEIS A171871: triangle A(N, R) = number of classifications of N elements
with exactly R binary partitions (Munafo). A039754: T(R, N) = number of
binary codes of length R with N words up to the hypercube group.
Conjecture (Munafo, Dec 30 2009): in each column R, the last 2^(R-1) values
of A171871 equal the first 2^(R-1) values of row R of A039754.

Definitions.
* `Word R = Fin R → Bool`; `actEquiv g` is the hypercube group element
  g = (σ, m): permute coordinates by σ, then flip the coordinates in m.
* `Equivalent C D`: some g maps the code C onto D.
* `T R N` (A039754): number of classes of N-word codes of length R.
* `IsClassification C`: the R columns of the code C are binary partitions
  of its words that are nontrivial (no constant column), pairwise distinct
  as partitions (no column equal or complementary to another), and none can
  be omitted without leaving two words unseparated (deleting any column
  makes two words equal). The words are separated by all columns because C
  is a set.
* `A N R` (A171871): number of classes of N-word codes of length R that are
  classifications.

Main theorems.
* `isClassification_of_card`: a code with more than 2^(R-1) words is a
  classification (deleting a coordinate cannot be injective on it).
* `A_eq_T`: 2^(R-1) < N → A N R = T R N.
* `T_compl`: N ≤ 2^R → T R (2^R - N) = T R N (complementing the code).
* `A171871_conjecture`: for R ≥ 1 and 1 ≤ k ≤ 2^(R-1),
  A (2^(R-1)+k) R = T R (2^(R-1)+k) = T R (2^(R-1)-k), i.e. the last
  2^(R-1) values of column R are the first 2^(R-1) values of row R of
  A039754 (in reverse order) and also the matching values of row R.

Not checked in this file: that a classification of N unlabeled elements by
a set of R binary partitions, up to isomorphism, is the same as a code of
the above kind up to the hypercube group (the encoding: list the
partitions, pick a side of each, write each element's word), and agreement
with the OEIS data (certificate/check.py, R ≤ 4).
-/
import Mathlib

open Finset

namespace A171871

abbrev Word (R : ℕ) := Fin R → Bool

/-- The hypercube group element `g = (σ, m)` acting on words. -/
def actEquiv {R : ℕ} (g : Equiv.Perm (Fin R) × (Fin R → Bool)) : Word R ≃ Word R where
  toFun w i := xor (g.2 i) (w (g.1.symm i))
  invFun w j := xor (g.2 (g.1 j)) (w (g.1 j))
  left_inv w := by funext j; simp
  right_inv w := by funext i; simp

def Equivalent {R : ℕ} (C D : Finset (Word R)) : Prop :=
  ∃ g : Equiv.Perm (Fin R) × (Fin R → Bool), C.image (actEquiv g) = D

def IsClassification {R : ℕ} (C : Finset (Word R)) : Prop :=
  (∀ i, ¬ ∃ b : Bool, ∀ w ∈ C, w i = b) ∧
  (∀ i j, i ≠ j → ¬ ∃ c : Bool, ∀ w ∈ C, w j = xor c (w i)) ∧
  (∀ i, ∃ u ∈ C, ∃ v ∈ C, u ≠ v ∧ ∀ j, j ≠ i → u j = v j)

/-- A039754 (T(R, N)). -/
noncomputable def T (R N : ℕ) : ℕ :=
  Nat.card (Quot (fun C D : {C : Finset (Word R) // C.card = N} => Equivalent C.1 D.1))

/-- A171871 (A(N, R)). -/
noncomputable def A (N R : ℕ) : ℕ :=
  Nat.card (Quot (fun C D : {C : Finset (Word R) // C.card = N ∧ IsClassification C} =>
    Equivalent C.1 D.1))

/-- Deleting coordinate `i`. -/
def del {R : ℕ} (i : Fin R) (w : Word R) : {j : Fin R // j ≠ i} → Bool := fun j => w j.1

lemma card_le_of_injOn {R : ℕ} (C : Finset (Word R)) (i : Fin R)
    (h : Set.InjOn (del i) C) : C.card ≤ 2 ^ (R - 1) := by
  have h1 := Finset.card_le_card_of_injOn (del i) (s := C) (t := Finset.univ)
    (by intro a _; simp) h
  have h2 : (Finset.univ : Finset ({j : Fin R // j ≠ i} → Bool)).card = 2 ^ (R - 1) := by
    simp [Finset.card_univ]
  omega

theorem isClassification_of_card {R : ℕ} (C : Finset (Word R))
    (hC : 2 ^ (R - 1) < C.card) : IsClassification C := by
  refine ⟨?_, ?_, ?_⟩
  · rintro i ⟨b, hb⟩
    refine absurd (card_le_of_injOn C i ?_) (by omega)
    intro u hu v hv huv
    funext j
    by_cases hj : j = i
    · subst hj; rw [hb u hu, hb v hv]
    · exact congrFun huv ⟨j, hj⟩
  · rintro i j hij ⟨c, hc⟩
    refine absurd (card_le_of_injOn C j ?_) (by omega)
    intro u hu v hv huv
    funext k
    by_cases hk : k = j
    · subst hk
      have : u i = v i := congrFun huv ⟨i, hij⟩
      rw [hc u hu, hc v hv, this]
    · exact congrFun huv ⟨k, hk⟩
  · intro i
    by_contra hne
    push Not at hne
    refine absurd (card_le_of_injOn C i ?_) (by omega)
    intro u hu v hv huv
    by_contra h
    obtain ⟨j, hj, hjne⟩ := hne u hu v hv h
    exact hjne (congrFun huv ⟨j, hj⟩)

theorem A_eq_T (N R : ℕ) (hN : 2 ^ (R - 1) < N) : A N R = T R N := by
  unfold A T
  apply Nat.card_congr
  refine Quot.congr (Equiv.subtypeEquivRight (fun C => ⟨fun h => h.1, fun h =>
    ⟨h, isClassification_of_card C (h ▸ hN)⟩⟩)) (fun a b => Iff.rfl)

lemma image_compl_equiv {R : ℕ} (e : Word R ≃ Word R) (C : Finset (Word R)) :
    (Cᶜ).image e = (C.image e)ᶜ := by
  ext x
  simp only [Finset.mem_image, Finset.mem_compl]
  constructor
  · rintro ⟨y, hy, rfl⟩ ⟨z, hz, hzy⟩
    exact hy (e.injective hzy ▸ hz)
  · intro hx
    exact ⟨e.symm x, fun h => hx ⟨e.symm x, h, by simp⟩, by simp⟩

theorem T_compl (R N : ℕ) (hN : N ≤ 2 ^ R) : T R (2 ^ R - N) = T R N := by
  unfold T
  apply Nat.card_congr
  have hu : (Finset.univ : Finset (Word R)).card = 2 ^ R := by simp
  let e : {C : Finset (Word R) // C.card = 2 ^ R - N} ≃ {C : Finset (Word R) // C.card = N} :=
    { toFun := fun C => ⟨C.1ᶜ, by rw [Finset.card_compl, Fintype.card_fun, C.2]; simp; omega⟩
      invFun := fun C => ⟨C.1ᶜ, by rw [Finset.card_compl, Fintype.card_fun, C.2]; simp⟩
      left_inv := fun C => by simp
      right_inv := fun C => by simp }
  refine Quot.congr e (fun a b => ?_)
  simp only [Equivalent, e, Equiv.coe_fn_mk]
  constructor
  · rintro ⟨g, hg⟩; exact ⟨g, by rw [image_compl_equiv, hg]⟩
  · rintro ⟨g, hg⟩
    refine ⟨g, ?_⟩
    rw [image_compl_equiv] at hg
    exact compl_injective hg

theorem A171871_conjecture (R k : ℕ) (hR : 1 ≤ R) (hk1 : 1 ≤ k) (hk : k ≤ 2 ^ (R - 1)) :
    A (2 ^ (R - 1) + k) R = T R (2 ^ (R - 1) + k) ∧
    A (2 ^ (R - 1) + k) R = T R (2 ^ (R - 1) - k) := by
  have hpow : 2 ^ R = 2 * 2 ^ (R - 1) := by
    rw [← pow_succ']; congr 1; omega
  have h1 : A (2 ^ (R - 1) + k) R = T R (2 ^ (R - 1) + k) := A_eq_T _ _ (by omega)
  refine ⟨h1, ?_⟩
  rw [h1, ← T_compl R (2 ^ (R - 1) + k) (by omega)]
  congr 1
  omega

