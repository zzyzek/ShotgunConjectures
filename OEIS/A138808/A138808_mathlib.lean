import Mathlib

/-
OEIS A138808: number of integer pairs (x,y), x > 0, y > 0, such that x <= p, y <= q for some
factorization n = p*q.  Conjecture (R. J. Mathar, 2008): the row sums of A010766
(row n: floor(n/k), k = 1..n) are upper bounds.

Definitions.
* `A138808 n` = `Set.ncard` of {(x,y) : 0 < x, 0 < y, ∃ p q, p * q = n, x ≤ p, y ≤ q}
  (the entry's definition read literally; the set is finite for n ≥ 1).
* `rowSum n` = ∑_{k=1..n} n / k (natural-number division = floor), the row sum of A010766.

Main theorem `A138808_le_rowSum`: for every n ≥ 1, A138808 n ≤ rowSum n.
Route: x ≤ p, y ≤ q, p q = n give x y ≤ n, so the set lies in
{(x,y) : 1 ≤ x, 1 ≤ y, x y ≤ n}, whose size is ∑_{x=1..n} #{y ≥ 1 : x y ≤ n} = ∑ n / x.
Not checked: nothing beyond reading the entry's definition as above.
-/

noncomputable def A138808 (n : ℕ) : ℕ :=
  Set.ncard {xy : ℕ × ℕ | 0 < xy.1 ∧ 0 < xy.2 ∧ ∃ p q, p * q = n ∧ xy.1 ≤ p ∧ xy.2 ≤ q}

def rowSum (n : ℕ) : ℕ := ∑ k ∈ Finset.Icc 1 n, n / k

/-- The hyperbola region {x, y ≥ 1, x y ≤ n} as a finset. -/
def hyp (n : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.Icc 1 n ×ˢ Finset.Icc 1 n).filter (fun xy => xy.1 * xy.2 ≤ n)

lemma subset_hyp (n : ℕ) :
    {xy : ℕ × ℕ | 0 < xy.1 ∧ 0 < xy.2 ∧ ∃ p q, p * q = n ∧ xy.1 ≤ p ∧ xy.2 ≤ q} ⊆
      (hyp n : Set (ℕ × ℕ)) := by
  rintro ⟨x, y⟩ ⟨hx, hy, p, q, hpq, hxp, hyq⟩
  have hxy : x * y ≤ n := hpq ▸ Nat.mul_le_mul hxp hyq
  have hxn : x ≤ n := le_trans (Nat.le_mul_of_pos_right x hy) hxy
  have hyn : y ≤ n := le_trans (Nat.le_mul_of_pos_left y hx) hxy
  simp only [hyp, Finset.coe_filter, Finset.mem_product, Finset.mem_Icc, Set.mem_ofPred_eq]
  exact ⟨⟨⟨hx, hxn⟩, ⟨hy, hyn⟩⟩, hxy⟩

lemma card_fiber (n x : ℕ) (hx : 1 ≤ x) :
    ((Finset.Icc 1 n).filter (fun y => x * y ≤ n)).card = n / x := by
  have : (Finset.Icc 1 n).filter (fun y => x * y ≤ n) = Finset.Icc 1 (n / x) := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨h1, _⟩, h2⟩
      exact ⟨h1, (Nat.le_div_iff_mul_le (by omega)).2 (by rw [Nat.mul_comm]; exact h2)⟩
    · rintro ⟨h1, h2⟩
      have h3 : y * x ≤ n := (Nat.le_div_iff_mul_le (by omega)).1 h2
      refine ⟨⟨h1, le_trans h2 (Nat.div_le_self n x)⟩, ?_⟩
      rw [Nat.mul_comm]; exact h3
  rw [this, Nat.card_Icc, Nat.add_sub_cancel]

lemma card_hyp (n : ℕ) : (hyp n).card = rowSum n := by
  unfold hyp rowSum
  rw [Finset.card_filter, Finset.sum_product]
  refine Finset.sum_congr rfl ?_
  intro x hx
  rw [← Finset.card_filter, card_fiber n x (Finset.mem_Icc.1 hx).1]

theorem A138808_le_rowSum (n : ℕ) : A138808 n ≤ rowSum n := by
  rw [← card_hyp, A138808]
  calc Set.ncard _ ≤ Set.ncard (hyp n : Set (ℕ × ℕ)) :=
        Set.ncard_le_ncard (subset_hyp n) (Finset.finite_toSet _)
    _ = (hyp n).card := Set.ncard_coe_finset _
