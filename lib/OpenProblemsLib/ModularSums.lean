import Mathlib

/-!
# Sums over `ZMod n` and maps missing one residue

Counting lemmas for arguments in the style of Monsky's modular `n`-queens bound (sums and sums
of squares of the coordinates of `n - 1` points, each coordinate map missing one residue).

Main results.
* `sum_zmod` : a sum over all of `ZMod n` equals the sum over the casts of `0, ..., n - 1`.
* `miss` : if `f : α → ZMod n` is injective on `S` and `|S| = n - 1`, there is one residue `a`
  with `∑_{x ∈ S} g (f x) = ∑_v g v - g a` for every `g` into any additive group.
* `sq_lift` : if `2 ∣ n` and `u ≡ w (mod n)` then `u² ≡ w² (mod 2n)`.

Used by Guy C18 (`NT/C18.4`, modular queens).
-/

namespace OpenProblemsLib.ModularSums

/-- A sum over `ZMod n` is the sum over the casts of `0, ..., n - 1`. -/
theorem sum_zmod {n : ℕ} [NeZero n] {R : Type*} [AddCommMonoid R] (g : ZMod n → R) :
    ∑ v, g v = ∑ i ∈ Finset.range n, g (i : ZMod n) := by
  refine (Finset.sum_nbij' (s := Finset.range n) (t := Finset.univ)
    (f := fun i => g (i : ZMod n)) (g := g) (fun i => (i : ZMod n)) (fun v => v.val)
    ?_ ?_ ?_ ?_ ?_).symm
  · intro i _; simp
  · intro v _; simp [ZMod.val_lt]
  · intro i hi; rw [Finset.mem_range] at hi; exact ZMod.val_cast_of_lt hi
  · intro v _; simp
  · intro i _; rfl

/-- If `f` is injective on `S` and `|S| = n - 1`, the image misses exactly one value `a`, so
the sum of `g ∘ f` over `S` is the full sum of `g` minus `g a`. -/
theorem miss {n : ℕ} [NeZero n] {α : Type*} [DecidableEq α] (S : Finset α) (f : α → ZMod n)
    (hf : Set.InjOn f S) (hc : S.card + 1 = n) :
    ∃ a : ZMod n, ∀ {R : Type} [AddCommGroup R] (g : ZMod n → R),
      ∑ p ∈ S, g (f p) = (∑ v, g v) - g a := by
  classical
  have hI : (S.image f).card = S.card := Finset.card_image_of_injOn hf
  have hcc : (S.image f)ᶜ.card = 1 := by
    rw [Finset.card_compl, hI, ZMod.card]; omega
  obtain ⟨a, ha⟩ := Finset.card_eq_one.1 hcc
  refine ⟨a, fun {R} _ g => ?_⟩
  rw [← Finset.sum_image (f := g) hf, ← Finset.sum_compl_add_sum (S.image f), ha,
    Finset.sum_singleton]
  abel

/-- If `2 ∣ n` and `u ≡ w (mod n)`, then `u² ≡ w² (mod 2n)`. -/
theorem sq_lift {n : ℕ} (hn : 2 ∣ n) (u w : ℤ) (h : ((u : ZMod n)) = (w : ZMod n)) :
    ((u : ZMod (2 * n))) ^ 2 = (w : ZMod (2 * n)) ^ 2 := by
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at h
  obtain ⟨k, hk⟩ := h
  obtain ⟨r, rfl⟩ := hn
  have : ((u : ZMod (2 * (2 * r)))) = (w : ZMod (2 * (2 * r))) + ((2 * r : ℕ) : ℤ) * (-k) := by
    have : u = w + ((2 * r : ℕ) : ℤ) * (-k) := by push_cast at hk ⊢; linarith
    rw [this]; push_cast; ring
  rw [this]
  have h0 : ((2 * (2 * r) : ℕ) : ZMod (2 * (2 * r))) = 0 := ZMod.natCast_self _
  have : ((w : ZMod (2 * (2 * r))) + ((2 * r : ℕ) : ℤ) * (-k)) ^ 2 =
      (w : ZMod (2 * (2 * r))) ^ 2 +
        ((2 * (2 * r) : ℕ) : ZMod (2 * (2 * r))) * (w * (-k) + r * k ^ 2) := by
    push_cast; ring
  rw [this, h0, zero_mul, add_zero]

end OpenProblemsLib.ModularSums
