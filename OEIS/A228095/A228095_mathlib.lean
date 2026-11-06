import Mathlib

/-
OEIS A228095 (Zhi-Wei Sun, 2013): determinant of the p X p matrix with (i,j)-entry the
Legendre symbol ((i^2 + 3ij + 3j^2)/p), i, j = 0..p-1, p = p_n.
Conjecture: a(n) = 0 if p_n ≡ 5 (mod 6).

Definitions.
* `M p : Matrix (Fin p) (Fin p) ℤ`, `M p i j = legendreSym p (i^2 + 3 i j + 3 j^2)`.

Main theorem.
* `A228095_conj : p % 6 = 5 → (M p).det = 0` (p prime, as `Fact p.Prime`).
Route: the vector v_j = (j/p) is a nonzero kernel vector. Row i of M v is
Σ_y χ(i^2 + 3iy + 3y^2) χ(y) (`row_zero`): for i = 0 it is χ(3) Σ χ(y^3) = 0; for i ≠ 0,
y = i t gives χ(i^3) Σ_t χ(t + 3t^2 + 3t^3), and t = 1/s turns the summand into
χ((s+1)^3 - 1) (`key_sum`); cubing is a bijection for p ≡ 2 (mod 3) (`cube_bij`), so the sum
is Σ_z χ(z - 1) = 0. The index map Fin p → ZMod p is a bijection (`cast_bij`).
Not checked here: the reading p = p_n (the theorem is for every prime p ≡ 5 mod 6);
agreement with the data (certificate/check.py).
-/

namespace OEIS_A228095

open Finset

variable {p : ℕ} [hp : Fact p.Prime]

local notation "χ" => quadraticChar (ZMod p)

theorem ringChar_ne_two (h5 : p % 6 = 5) : ringChar (ZMod p) ≠ 2 := by
  rw [ZMod.ringChar_zmod_n]; omega

theorem char_sum_zero (h5 : p % 6 = 5) : ∑ x : ZMod p, χ x = 0 :=
  quadraticChar_sum_zero (ringChar_ne_two h5)

/-- For p ≡ 2 (mod 3), cubing is a bijection of ZMod p. -/
theorem cube_bij (h5 : p % 6 = 5) : Function.Bijective (fun x : ZMod p => x ^ 3) := by
  have hinj : Function.Injective (fun x : ZMod p => x ^ 3) := by
    intro x y hxy
    have key : ∀ z : ZMod p, (z ^ 3) ^ ((2 * p - 1) / 3) = z := by
      intro z
      have e : 3 * ((2 * p - 1) / 3) = p + (p - 1) := by omega
      rw [← pow_mul, e, pow_add, ZMod.pow_card]
      rcases eq_or_ne z 0 with rfl | hz
      · simp
      · rw [ZMod.pow_card_sub_one_eq_one hz, mul_one]
    have := congrArg (fun w => w ^ ((2 * p - 1) / 3)) hxy
    simp only at this
    rwa [key, key] at this
  exact (Finite.injective_iff_bijective).mp hinj

theorem sum_cube_sub_one (h5 : p % 6 = 5) : ∑ w : ZMod p, χ (w ^ 3 - 1) = 0 := by
  rw [(cube_bij h5).sum_comp (fun z => χ (z - 1))]
  rw [Fintype.sum_equiv (Equiv.subRight (1 : ZMod p)) (fun z => χ (z - 1)) (fun z => χ z)
    (fun z => rfl)]
  exact char_sum_zero h5

theorem key_sum (h5 : p % 6 = 5) : ∑ t : ZMod p, χ (t + 3 * t ^ 2 + 3 * t ^ 3) = 0 := by
  rw [← Fintype.sum_equiv (Equiv.inv (ZMod p)) (fun s => χ (s⁻¹ + 3 * s⁻¹ ^ 2 + 3 * s⁻¹ ^ 3))
    (fun t => χ (t + 3 * t ^ 2 + 3 * t ^ 3)) (fun s => by simp)]
  have e : ∀ s : ZMod p, χ (s⁻¹ + 3 * s⁻¹ ^ 2 + 3 * s⁻¹ ^ 3) = χ ((s + 1) ^ 3 - 1) := by
    intro s
    rcases eq_or_ne s 0 with rfl | hs
    · simp
    · have h1 : s⁻¹ + 3 * s⁻¹ ^ 2 + 3 * s⁻¹ ^ 3 = (s⁻¹ ^ 2) ^ 2 * ((s + 1) ^ 3 - 1) := by
        field_simp; ring
      rw [h1, map_mul, quadraticChar_sq_one' (pow_ne_zero 2 (inv_ne_zero hs)), one_mul]
  rw [Finset.sum_congr rfl (fun s _ => e s)]
  rw [Fintype.sum_equiv (Equiv.addRight (1 : ZMod p)) (fun s => χ ((s + 1) ^ 3 - 1))
    (fun w => χ (w ^ 3 - 1)) (fun s => rfl)]
  exact sum_cube_sub_one h5

/-- Row i of the matrix applied to (χ(j))_j vanishes. -/
theorem row_zero (h5 : p % 6 = 5) (i : ZMod p) :
    ∑ y : ZMod p, χ (i ^ 2 + 3 * i * y + 3 * y ^ 2) * χ y = 0 := by
  rcases eq_or_ne i 0 with rfl | hi
  · have e : ∀ y : ZMod p, χ (0 ^ 2 + 3 * 0 * y + 3 * y ^ 2) * χ y = χ 3 * χ (y ^ 3) := by
      intro y; rw [← map_mul, ← map_mul]; ring_nf
    rw [Finset.sum_congr rfl (fun y _ => e y), ← Finset.mul_sum,
      (cube_bij h5).sum_comp (fun z => χ z), char_sum_zero h5, mul_zero]
  · have e : ∀ t : ZMod p, χ (i ^ 2 + 3 * i * (i * t) + 3 * (i * t) ^ 2) * χ (i * t) =
        χ (i ^ 3) * χ (t + 3 * t ^ 2 + 3 * t ^ 3) := by
      intro t; rw [← map_mul, ← map_mul]; ring_nf
    rw [← Fintype.sum_equiv (Equiv.mulLeft₀ i hi) (fun t => χ (i ^ 2 + 3 * i * (i * t) +
      3 * (i * t) ^ 2) * χ (i * t)) _ (fun t => rfl)]
    rw [Finset.sum_congr rfl (fun t _ => e t), ← Finset.mul_sum, key_sum h5, mul_zero]

/-- A228095: the p × p matrix ((i^2 + 3ij + 3j^2)/p), i, j = 0..p-1. -/
def M (p : ℕ) [Fact p.Prime] : Matrix (Fin p) (Fin p) ℤ :=
  fun i j => legendreSym p ((i : ℤ) ^ 2 + 3 * i * j + 3 * (j : ℤ) ^ 2)

theorem cast_bij : Function.Bijective (fun j : Fin p => ((j : ℕ) : ZMod p)) := by
  have hinj : Function.Injective (fun j : Fin p => ((j : ℕ) : ZMod p)) := by
    intro a b h
    simp only at h
    rw [ZMod.natCast_eq_natCast_iff'] at h
    rw [Nat.mod_eq_of_lt a.2, Nat.mod_eq_of_lt b.2] at h
    exact Fin.ext h
  rw [Fintype.bijective_iff_injective_and_card]
  exact ⟨hinj, by simp⟩

/-- Conjecture of A228095: the determinant vanishes when p ≡ 5 (mod 6). -/
theorem A228095_conj (h5 : p % 6 = 5) : (M p).det = 0 := by
  rw [← Matrix.exists_mulVec_eq_zero_iff]
  refine ⟨fun j => legendreSym p (j : ℤ), ?_, ?_⟩
  · intro h
    have hp1 : 1 < p := hp.out.one_lt
    have := congrFun h ⟨1, hp1⟩
    simp [legendreSym] at this
  · funext i
    simp only [Matrix.mulVec, dotProduct, M, legendreSym, Pi.zero_apply]
    push_cast
    have := (cast_bij (p := p)).sum_comp
      (fun y : ZMod p => χ (((i : ℕ) : ZMod p) ^ 2 + 3 * ((i : ℕ) : ZMod p) * y + 3 * y ^ 2) * χ y)
    rw [this]
    exact row_zero h5 _
