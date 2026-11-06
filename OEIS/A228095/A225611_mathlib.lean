import Mathlib

/-
OEIS A225611 (Zhi-Wei Sun, 2013): determinant of the (p-1) X (p-1) matrix with (i,j)-entry
the Legendre symbol ((i^2 + 6ij + j^2)/p), i, j = 1..p-1, p = p_n.
Conjecture: a(n) = 0 if p_n ≡ 3 (mod 4).

Definitions.
* `M p : Matrix (Fin (p-1)) (Fin (p-1)) ℤ`, index k standing for k + 1.

Main theorem.
* `A225611_conj : p % 4 = 3 → (M p).det = 0` (p prime, as `Fact p.Prime`).
Route: v_j = (j/p) is a nonzero kernel vector; with y = a t, row a of M v is
χ(a^3) S where S = Σ_t χ(t + 6t^2 + t^3) (`row_zero`). `S_zero`: since -1 is a non-square,
2 S = Σ_u g(u^2) + Σ_u g(-u^2) (`sum_split`, from #{u : u^2 = t} = 1 + χ(t)), which reduces S
to Σ_u χ(u^4 + 6u^2 + 1) - Σ_u χ(u^4 - 6u^2 + 1). Both sums are -1 (`U_sum`, `T_sum`): the
substitution u ↦ (1+u)/(1-u) (`mobius_sum`) maps u^4 - 6u^2 + 1 to -4(...)/(1-u)^4 (so that
sum is odd up to the end points) and u^4 + 6u^2 + 1 to 8(1 + u^4)/(1-u)^4, and
Σ_u χ(1 + u^4) = -1 (`sum_one_add_four`, via Σ_t χ(t^2+1) = -1 and Σ_t χ(t^3+t) = 0).
Not checked here: the reading p = p_n (the theorem is for every prime p ≡ 3 mod 4);
agreement with the data (certificate/check.py).
-/

namespace OEIS_A225611

open Finset

variable {p : ℕ} [hp : Fact p.Prime]

local notation "χ" => quadraticChar (ZMod p)

theorem hF (h3 : p % 4 = 3) : ringChar (ZMod p) ≠ 2 := by
  rw [ZMod.ringChar_zmod_n]; omega

theorem chi_neg_one (h3 : p % 4 = 3) : χ (-1) = -1 := by
  classical
  rw [quadraticChar_neg_one (hF h3), ZMod.card, ZMod.χ₄_nat_three_mod_four h3]

theorem chi_sum (h3 : p % 4 = 3) : ∑ x : ZMod p, χ x = 0 := quadraticChar_sum_zero (hF h3)

theorem chi_shift_sum (h3 : p % 4 = 3) (c : ZMod p) : ∑ x : ZMod p, χ (x + c) = 0 := by
  rw [Fintype.sum_equiv (Equiv.addRight c) (fun x => χ (x + c)) (fun y => χ y) (fun x => rfl)]
  exact chi_sum h3

/-- Σ_u g(u²) = Σ_t (χ t + 1) g t. -/
theorem sum_sq (h3 : p % 4 = 3) (g : ZMod p → ℤ) :
    ∑ u : ZMod p, g (u ^ 2) = ∑ t : ZMod p, (χ t + 1) * g t := by
  classical
  rw [← Finset.sum_fiberwise Finset.univ (fun u : ZMod p => u ^ 2) (fun u => g (u ^ 2))]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  have hc := quadraticChar_card_sqrts (hF h3) t
  rw [Finset.sum_congr rfl (fun u hu => by rw [(Finset.mem_filter.mp hu).2]), Finset.sum_const,
    nsmul_eq_mul]
  congr 1
  rw [← hc]
  simp

/-- Σ_t g t = (Σ_u g(u²) + Σ_u g(-u²)) / 2. -/
theorem sum_split (h3 : p % 4 = 3) (g : ZMod p → ℤ) :
    2 * ∑ t : ZMod p, g t = ∑ u : ZMod p, g (u ^ 2) + ∑ u : ZMod p, g (-(u ^ 2)) := by
  rw [sum_sq h3 g, sum_sq h3 (fun t => g (-t))]
  rw [Fintype.sum_equiv (Equiv.neg (ZMod p)) (fun t => (χ t + 1) * g (-t))
    (fun s => (χ (-s) + 1) * g s) (fun t => by simp)]
  rw [← Finset.sum_add_distrib, Finset.mul_sum]
  · refine Finset.sum_congr rfl (fun s _ => ?_)
    rw [show -s = (-1) * s by ring, map_mul, chi_neg_one h3]; ring

/-- Σ_s χ(s² + s) = -1. -/
theorem sum_s_sq_add_s (h3 : p % 4 = 3) : ∑ s : ZMod p, χ (s ^ 2 + s) = -1 := by
  rw [← Fintype.sum_equiv (Equiv.inv (ZMod p)) (fun r => χ (r⁻¹ ^ 2 + r⁻¹)) _ (fun r => by simp)]
  have e : ∀ r : ZMod p, χ (r⁻¹ ^ 2 + r⁻¹) = χ (1 + r) - (if r = 0 then 1 else 0) := by
    intro r
    rcases eq_or_ne r 0 with rfl | hr
    · simp
    · have : r⁻¹ ^ 2 + r⁻¹ = (r⁻¹) ^ 2 * (1 + r) := by field_simp
      rw [this, map_mul, quadraticChar_sq_one' (inv_ne_zero hr), one_mul]
      simp [hr]
  rw [Finset.sum_congr rfl (fun r _ => e r), Finset.sum_sub_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [show (∑ r : ZMod p, χ (1 + r)) = ∑ r : ZMod p, χ (r + 1) by
    exact Finset.sum_congr rfl (fun r _ => by rw [add_comm]), chi_shift_sum h3]
  ring

/-- Σ_t χ(t² + 1) = -1. -/
theorem sum_t_sq_add_one (h3 : p % 4 = 3) : ∑ t : ZMod p, χ (t ^ 2 + 1) = -1 := by
  rw [sum_sq h3 (fun s => χ (s + 1))]
  have : ∀ s : ZMod p, (χ s + 1) * χ (s + 1) = χ (s ^ 2 + s) + χ (s + 1) := by
    intro s; rw [add_mul, one_mul, ← map_mul]; ring_nf
  rw [Finset.sum_congr rfl (fun s _ => this s), Finset.sum_add_distrib, sum_s_sq_add_s h3,
    chi_shift_sum h3]
  ring

/-- Σ_u χ(1 + u⁴) = -1. -/
theorem sum_one_add_four (h3 : p % 4 = 3) : ∑ u : ZMod p, χ (1 + u ^ 4) = -1 := by
  have e : ∀ u : ZMod p, χ (1 + u ^ 4) = χ ((u ^ 2) ^ 2 + 1) := fun u => by ring_nf
  rw [Finset.sum_congr rfl (fun u _ => e u), sum_sq h3 (fun t => χ (t ^ 2 + 1))]
  have : ∀ t : ZMod p, (χ t + 1) * χ (t ^ 2 + 1) = χ (t ^ 3 + t) + χ (t ^ 2 + 1) := by
    intro t; rw [add_mul, one_mul, ← map_mul]; ring_nf
  rw [Finset.sum_congr rfl (fun t _ => this t), Finset.sum_add_distrib, sum_t_sq_add_one h3]
  have hodd : ∑ t : ZMod p, χ (t ^ 3 + t) = 0 := by
    have h := Fintype.sum_equiv (Equiv.neg (ZMod p)) (fun t => χ (t ^ 3 + t))
      (fun t => -χ (t ^ 3 + t)) (fun t => by
        simp only [Equiv.neg_apply]
        rw [show (-t) ^ 3 + -t = (-1) * (t ^ 3 + t) by ring, map_mul, chi_neg_one h3]; ring)
    rw [Finset.sum_neg_distrib] at h
    linarith
  rw [hodd]; ring

theorem two_ne (h3 : p % 4 = 3) : (2 : ZMod p) ≠ 0 := by
  intro h
  have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at this
  have := Nat.le_of_dvd (by norm_num) this
  have := hp.out.two_le
  omega

/-- The Möbius map u ↦ (1+u)/(1-u) is a bijection from u ≠ 1 to w ≠ -1. -/
theorem mobius_sum (h3 : p % 4 = 3) (f : ZMod p → ℤ) :
    ∑ u ∈ univ.erase (1 : ZMod p), f ((1 + u) / (1 - u)) = ∑ w ∈ univ.erase (-1 : ZMod p), f w := by
  have h2 := two_ne h3
  refine Finset.sum_nbij' (fun u => (1 + u) / (1 - u)) (fun w => (w - 1) / (w + 1)) ?_ ?_ ?_ ?_ ?_
  · intro u hu
    have hu1 : u ≠ 1 := Finset.ne_of_mem_erase hu
    have hsub : (1 : ZMod p) - u ≠ 0 := sub_ne_zero.mpr (Ne.symm hu1)
    refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩
    intro h
    rw [div_eq_iff hsub] at h
    apply h2; linear_combination h
  · intro w hw
    have hw1 : w ≠ -1 := Finset.ne_of_mem_erase hw
    have hadd : w + 1 ≠ 0 := by intro h; apply hw1; linear_combination h
    refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩
    intro h
    rw [div_eq_iff hadd] at h
    apply h2; linear_combination -h
  · intro u hu
    have hu1 : u ≠ 1 := Finset.ne_of_mem_erase hu
    have hsub : (1 : ZMod p) - u ≠ 0 := sub_ne_zero.mpr (Ne.symm hu1)
    field_simp
    ring_nf
    field_simp
  · intro w hw
    have hw1 : w ≠ -1 := Finset.ne_of_mem_erase hw
    have hadd : w + 1 ≠ 0 := by intro h; apply hw1; linear_combination h
    field_simp
    ring_nf
    field_simp
  · intro u _; rfl

theorem chi_four (h3 : p % 4 = 3) : χ 4 = 1 := by
  rw [show (4 : ZMod p) = 2 ^ 2 by norm_num]
  exact quadraticChar_sq_one' (two_ne h3)

theorem T_sum (h3 : p % 4 = 3) : ∑ u : ZMod p, χ (u ^ 4 - 6 * u ^ 2 + 1) = -1 := by
  have h2 := two_ne h3
  set A := ∑ u : ZMod p, χ (u ^ 4 - 6 * u ^ 2 + 1)
  have hm := mobius_sum h3 (fun w => χ (w ^ 4 - 6 * w ^ 2 + 1))
  have hodd : ∀ u ∈ univ.erase (1 : ZMod p),
      χ (((1 + u) / (1 - u)) ^ 4 - 6 * ((1 + u) / (1 - u)) ^ 2 + 1) = -χ (u ^ 4 - 6 * u ^ 2 + 1) := by
    intro u hu
    have hsub : (1 : ZMod p) - u ≠ 0 := sub_ne_zero.mpr (Ne.symm (Finset.ne_of_mem_erase hu))
    have e : ((1 + u) / (1 - u)) ^ 4 - 6 * ((1 + u) / (1 - u)) ^ 2 + 1 =
        (-1) * (2 * ((1 - u)⁻¹) ^ 2) ^ 2 * (u ^ 4 - 6 * u ^ 2 + 1) := by
      field_simp; ring
    rw [e, map_mul, map_mul, chi_neg_one h3,
      quadraticChar_sq_one' (mul_ne_zero h2 (pow_ne_zero 2 (inv_ne_zero hsub)))]
    ring
  rw [Finset.sum_congr rfl hodd, Finset.sum_neg_distrib] at hm
  have e1 := Finset.sum_erase_add univ (fun u : ZMod p => χ (u ^ 4 - 6 * u ^ 2 + 1)) (mem_univ 1)
  have e2 := Finset.sum_erase_add univ (fun u : ZMod p => χ (u ^ 4 - 6 * u ^ 2 + 1)) (mem_univ (-1))
  have v1 : χ ((1 : ZMod p) ^ 4 - 6 * 1 ^ 2 + 1) = -1 := by
    rw [show (1 : ZMod p) ^ 4 - 6 * 1 ^ 2 + 1 = (-1) * 4 by ring, map_mul, chi_neg_one h3,
      chi_four h3]; ring
  have v2 : χ ((-1 : ZMod p) ^ 4 - 6 * (-1) ^ 2 + 1) = -1 := by
    rw [show (-1 : ZMod p) ^ 4 - 6 * (-1) ^ 2 + 1 = (-1) * 4 by ring, map_mul, chi_neg_one h3,
      chi_four h3]; ring
  rw [v1] at e1; rw [v2] at e2
  linarith

theorem U_sum (h3 : p % 4 = 3) : ∑ u : ZMod p, χ (u ^ 4 + 6 * u ^ 2 + 1) = -1 := by
  have h2 := two_ne h3
  have hm := mobius_sum h3 (fun w => χ (w ^ 4 + 6 * w ^ 2 + 1))
  have hmap : ∀ u ∈ univ.erase (1 : ZMod p),
      χ (((1 + u) / (1 - u)) ^ 4 + 6 * ((1 + u) / (1 - u)) ^ 2 + 1) = χ 2 * χ (1 + u ^ 4) := by
    intro u hu
    have hsub : (1 : ZMod p) - u ≠ 0 := sub_ne_zero.mpr (Ne.symm (Finset.ne_of_mem_erase hu))
    have e : ((1 + u) / (1 - u)) ^ 4 + 6 * ((1 + u) / (1 - u)) ^ 2 + 1 =
        2 * (2 * ((1 - u)⁻¹) ^ 2) ^ 2 * (1 + u ^ 4) := by
      field_simp; ring
    rw [e, map_mul, map_mul,
      quadraticChar_sq_one' (mul_ne_zero h2 (pow_ne_zero 2 (inv_ne_zero hsub)))]
    ring
  rw [Finset.sum_congr rfl hmap, ← Finset.mul_sum] at hm
  have e1 := Finset.sum_erase_add univ (fun u : ZMod p => χ (1 + u ^ 4)) (mem_univ 1)
  have e2 := Finset.sum_erase_add univ (fun u : ZMod p => χ (u ^ 4 + 6 * u ^ 2 + 1)) (mem_univ (-1))
  rw [sum_one_add_four h3] at e1
  have v2 : χ ((-1 : ZMod p) ^ 4 + 6 * (-1) ^ 2 + 1) = χ 2 := by
    rw [show (-1 : ZMod p) ^ 4 + 6 * (-1) ^ 2 + 1 = 2 * 4 by ring, map_mul, chi_four h3, mul_one]
  rw [v2] at e2
  have v1 : (1 : ZMod p) + 1 ^ 4 = 2 := by ring
  rw [v1] at e1
  have hsq : χ 2 * χ 2 = 1 := by rw [← pow_two]; exact quadraticChar_sq_one h2
  have : ∑ u ∈ univ.erase (1 : ZMod p), χ (1 + u ^ 4) = -1 - χ 2 := by linarith
  rw [this] at hm
  nlinarith

/-- The elliptic character sum Σ_t χ(t + 6t² + t³) vanishes for p ≡ 3 (mod 4). -/
theorem S_zero (h3 : p % 4 = 3) : ∑ t : ZMod p, χ (t + 6 * t ^ 2 + t ^ 3) = 0 := by
  have hs := sum_split h3 (fun t => χ (t + 6 * t ^ 2 + t ^ 3))
  have hU : ∑ u : ZMod p, χ (u ^ 2 + 6 * (u ^ 2) ^ 2 + (u ^ 2) ^ 3) = -2 := by
    have e : ∀ u : ZMod p, χ (u ^ 2 + 6 * (u ^ 2) ^ 2 + (u ^ 2) ^ 3) =
        χ (u ^ 4 + 6 * u ^ 2 + 1) - (if u = 0 then 1 else 0) := by
      intro u
      rcases eq_or_ne u 0 with rfl | hu
      · simp
      · rw [show u ^ 2 + 6 * (u ^ 2) ^ 2 + (u ^ 2) ^ 3 = u ^ 2 * (u ^ 4 + 6 * u ^ 2 + 1) by ring,
          map_mul, quadraticChar_sq_one' hu]
        simp [hu]
    rw [Finset.sum_congr rfl (fun u _ => e u), Finset.sum_sub_distrib, U_sum h3]
    simp
  have hT : ∑ u : ZMod p, χ (-u ^ 2 + 6 * (-u ^ 2) ^ 2 + (-u ^ 2) ^ 3) = 2 := by
    have e : ∀ u : ZMod p, χ (-u ^ 2 + 6 * (-u ^ 2) ^ 2 + (-u ^ 2) ^ 3) =
        -χ (u ^ 4 - 6 * u ^ 2 + 1) + (if u = 0 then 1 else 0) := by
      intro u
      rcases eq_or_ne u 0 with rfl | hu
      · simp
      · rw [show -u ^ 2 + 6 * (-u ^ 2) ^ 2 + (-u ^ 2) ^ 3 =
            (-1) * u ^ 2 * (u ^ 4 - 6 * u ^ 2 + 1) by ring,
          map_mul, map_mul, quadraticChar_sq_one' hu, chi_neg_one h3]
        simp [hu]
    rw [Finset.sum_congr rfl (fun u _ => e u), Finset.sum_add_distrib, Finset.sum_neg_distrib,
      T_sum h3]
    simp
  have h' : ∑ u : ZMod p, χ (-(u ^ 2) + 6 * (-(u ^ 2)) ^ 2 + (-(u ^ 2)) ^ 3) = 2 := hT
  rw [hU, h'] at hs
  linarith

theorem row_zero (h3 : p % 4 = 3) (a : ZMod p) (ha : a ≠ 0) :
    ∑ y : ZMod p, χ (a ^ 2 + 6 * a * y + y ^ 2) * χ y = 0 := by
  have e : ∀ t : ZMod p, χ (a ^ 2 + 6 * a * (a * t) + (a * t) ^ 2) * χ (a * t) =
      χ (a ^ 3) * χ (t + 6 * t ^ 2 + t ^ 3) := by
    intro t; rw [← map_mul, ← map_mul]; ring_nf
  rw [← Fintype.sum_equiv (Equiv.mulLeft₀ a ha) (fun t => χ (a ^ 2 + 6 * a * (a * t) +
    (a * t) ^ 2) * χ (a * t)) _ (fun t => rfl)]
  rw [Finset.sum_congr rfl (fun t _ => e t), ← Finset.mul_sum, S_zero h3, mul_zero]

/-- A225611: the (p-1) × (p-1) matrix ((i^2 + 6ij + j^2)/p), i, j = 1..p-1
(index k : Fin (p-1) stands for k + 1). -/
def M (p : ℕ) [Fact p.Prime] : Matrix (Fin (p - 1)) (Fin (p - 1)) ℤ :=
  fun i j => legendreSym p (((i : ℤ) + 1) ^ 2 + 6 * ((i : ℤ) + 1) * ((j : ℤ) + 1) + ((j : ℤ) + 1) ^ 2)

theorem cast_ne_zero (j : Fin (p - 1)) : (((j : ℕ) + 1 : ℕ) : ZMod p) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff]
  intro h
  have := Nat.le_of_dvd (by omega) h
  have := j.2
  have := hp.out.two_le
  omega

theorem sum_fin (g : ZMod p → ℤ) (h0 : g 0 = 0) :
    ∑ j : Fin (p - 1), g (((j : ℕ) + 1 : ℕ) : ZMod p) = ∑ y : ZMod p, g y := by
  rw [← Finset.sum_erase_add univ g (mem_univ 0), h0, add_zero]
  refine Finset.sum_bij (fun j _ => (((j : ℕ) + 1 : ℕ) : ZMod p)) ?_ ?_ ?_ (fun _ _ => rfl)
  · intro j _
    exact Finset.mem_erase.mpr ⟨cast_ne_zero j, mem_univ _⟩
  · intro a _ b _ h
    rw [ZMod.natCast_eq_natCast_iff'] at h
    have ha := a.2; have hb := b.2
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h
    exact Fin.ext (by omega)
  · intro y hy
    have hy0 : y ≠ 0 := Finset.ne_of_mem_erase hy
    have hv : y.val ≠ 0 := by rwa [Ne, ZMod.val_eq_zero]
    have hlt : y.val < p := ZMod.val_lt y
    refine ⟨⟨y.val - 1, by omega⟩, mem_univ _, ?_⟩
    simp only
    rw [show y.val - 1 + 1 = y.val by omega, ZMod.natCast_zmod_val]

/-- Conjecture of A225611: the determinant vanishes when p ≡ 3 (mod 4). -/
theorem A225611_conj (h3 : p % 4 = 3) : (M p).det = 0 := by
  rw [← Matrix.exists_mulVec_eq_zero_iff]
  refine ⟨fun j => legendreSym p ((j : ℤ) + 1), ?_, ?_⟩
  · intro h
    have hp1 : 0 < p - 1 := by have := hp.out.two_le; omega
    have := congrFun h ⟨0, hp1⟩
    simp [legendreSym] at this
  · funext i
    simp only [Matrix.mulVec, dotProduct, M, legendreSym, Pi.zero_apply]
    have key := sum_fin (p := p)
      (fun y => χ ((((i : ℕ) + 1 : ℕ) : ZMod p) ^ 2 + 6 * (((i : ℕ) + 1 : ℕ) : ZMod p) * y + y ^ 2) * χ y)
      (by simp)
    push_cast at key ⊢
    rw [key]
    have := row_zero h3 (((i : ℕ) + 1 : ℕ) : ZMod p) (cast_ne_zero i)
    push_cast at this
    exact this
