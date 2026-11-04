/-
OEIS A110320 (number of blocks in all RNA secondary structures with n nodes),
conjecture of G. McGarvey (2007): a(n) = (A051292(n+2) - A051286(n+1))/2.

Main theorem `A110320_main` (and `A110320_main_nat`, the same identity in ℕ):
for every n,
  rnaBlockCount n = (crownCount (n+2) - fenceCount (n+1)) / 2,
where the three sequences are defined combinatorially, following the OEIS names.
* `rnaBlockCount n` (A110320): an RNA secondary structure on the nodes
  0, ..., n-1 is a set of arcs (i, j) with i + 2 ≤ j < n, no node in two arcs,
  and no two arcs crossing (i < k < j < l).  Viewed as a noncrossing partition
  its blocks are the arcs and the unpaired nodes; `rnaBlockCount n` sums
  (#arcs + #unpaired nodes) over all structures (`rna 0 n`, a Finset).
* `fenceCount n` (A051286): the fence of order 2n is x1 < x2 > x3 < ... < x2n,
  here the elements 0, ..., 2n-1 with order `fenceLE` (x ≤ y iff x = y, or y is
  odd, i.e. a maximum, and x is adjacent to y).  `fenceCount n` counts the
  order ideals (down-closed subsets) with n elements.
* `crownCount n` (A051292): the crown of size 2n is the fence closed up into a
  cycle, x2n > x1 (order `crownLE`, indices taken mod 2n); `crownCount n` counts
  its order ideals with n elements.  For n ≥ 2 this is the genuine crown; the
  theorem only uses n + 2 ≥ 2.  (OEIS sets A051292(0) = 2, which the definition
  does not reproduce and the theorem does not use.)
The identity holds for all n ≥ 0; A110320 has offset 1.

How it is proved.  The RNA counts satisfy the first-node recurrences
(`rna_sum`, a bijection on Finsets), giving S = 1 + zS + z²(S-1)S for the
structure series and W·R = S - 1 for the block series, with
R = 1 - z + z² - 2z²S (`Wser_mul_R`).  Fence ideals of size m + h correspond to
words over {D, H, U} (pairs 00, 10, 11) of height h avoiding the factor UD
(`fence_sum`, `Gp_true_eq`); crown ideals are the fence ideals except those
starting with D and ending with U, counted by F(n-2) (`crownIdeals_eq`,
`crownCount_eq`).  First- and last-visit decompositions of such words
(`firstvisit`, `lastvisit`) give F = S + z²S²F, hence F·R = 1 (`Fser_mul_R`).
Moreover R² = 1 - 2z - z² - 2z³ + z⁴ and R has constant coefficient 1
(`Rser_sq`, `Rser_const`, `Rser_unique`), so R is the square root in the
printed generating functions, and `fence_gf`, `crown_gf` (n ≥ 2), `blocks_gf`
show that the combinatorial sequences are the coefficients of the printed
g.f.s (`a051286`, `a051292`, `a110320` below).  The main theorem then follows
from `A110320_gf_identity`, the g.f. algebra.

Not checked here: nothing beyond the reading of the OEIS definitions above.
The fence order `fenceLE` is shown to be a partial order (`fenceLE_order`);
the crown order is used only through `crownLE_iff`.
-/
import Mathlib

open Finset PowerSeries

/-! ### Algebra of the printed generating functions -/

section GF

variable (R : ℚ⟦X⟧)

noncomputable def a051286 (n : ℕ) : ℚ := coeff n R⁻¹
noncomputable def a051292 (n : ℕ) : ℚ := coeff n ((1 - X ^ 2 + R) * R⁻¹)
noncomputable def a110320 (n : ℕ) : ℚ := coeff (n + 2) ((1 - X - X ^ 2) * R⁻¹ - 1) / 2

theorem A110320_gf_identity (hR : constantCoeff R = 1) (n : ℕ) :
    a110320 R n = (a051292 R (n + 2) - a051286 R (n + 1)) / 2 := by
  have hinv : R * R⁻¹ = 1 := PowerSeries.mul_inv_cancel R (by rw [hR]; norm_num)
  have e1 : (1 - X ^ 2 + R) * R⁻¹ = (1 - X - X ^ 2) * R⁻¹ + X * R⁻¹ + 1 := by
    rw [add_mul, hinv]; ring
  have e2 : coeff (n + 2) (X * R⁻¹) = coeff (n + 1) R⁻¹ := coeff_succ_X_mul (n + 1) _
  have e3 : coeff (n + 2) (1 : ℚ⟦X⟧) = 0 := by rw [coeff_one]; simp
  simp only [a110320, a051292, a051286]
  rw [e1, map_add, map_add, e2, e3, map_sub, e3]
  ring

end GF

/-! ### RNA secondary structures -/



def IsRNA (a b : ℕ) (A : Finset (ℕ × ℕ)) : Prop :=
  (∀ p ∈ A, a ≤ p.1 ∧ p.1 + 2 ≤ p.2 ∧ p.2 < b) ∧
  (∀ p ∈ A, ∀ q ∈ A, (p.1 = q.1 ∨ p.1 = q.2 ∨ p.2 = q.1 ∨ p.2 = q.2) → p = q) ∧
  (∀ p ∈ A, ∀ q ∈ A, ¬ (p.1 < q.1 ∧ q.1 < p.2 ∧ p.2 < q.2))

instance (a b : ℕ) : DecidablePred (IsRNA a b) := fun A => by
  unfold IsRNA; infer_instance

def rna (a b : ℕ) : Finset (Finset (ℕ × ℕ)) :=
  ((Ico a b ×ˢ Ico a b).powerset).filter (IsRNA a b)

theorem mem_rna {a b : ℕ} {A : Finset (ℕ × ℕ)} : A ∈ rna a b ↔ IsRNA a b A := by
  unfold rna
  simp only [mem_filter, mem_powerset, and_iff_right_iff_imp]
  intro h p hp
  have := h.1 p hp
  simp only [mem_product, mem_Ico]
  omega

theorem rna_self (a : ℕ) : rna a a = {∅} := by
  ext A
  rw [mem_rna, mem_singleton]
  constructor
  · intro h
    rw [eq_empty_iff_forall_notMem]
    intro p hp
    have := h.1 p hp
    omega
  · rintro rfl
    simp [IsRNA]

theorem rna_fiber_sum (f : Finset (ℕ × ℕ) → ℚ) {a b c : ℕ} (hc1 : a + 2 ≤ c) (hc2 : c < b) :
    ∑ A ∈ (rna a b).filter (fun A => (a, c) ∈ A), f A =
      ∑ X ∈ rna (a + 1) c, ∑ Y ∈ rna (c + 1) b, f (insert (a, c) (X ∪ Y)) := by
  rw [← sum_product']
  symm
  apply sum_nbij' (fun XY => insert (a, c) (XY.1 ∪ XY.2))
    (fun A => (A.filter (fun p => p.2 < c), A.filter (fun p => c < p.1)))
  · rintro ⟨X, Y⟩ hXY
    simp only [mem_product, mem_rna] at hXY
    obtain ⟨hX, hY⟩ := hXY
    simp only [mem_filter, mem_rna, mem_insert, true_or, and_true]
    refine ⟨?_, ?_, ?_⟩
    · intro p hp
      simp only [mem_insert, mem_union] at hp
      rcases hp with rfl | hp | hp
      · dsimp only; omega
      · have := hX.1 p hp; omega
      · have := hY.1 p hp; omega
    · intro p hp q hq
      simp only [mem_insert, mem_union] at hp hq
      rcases hp with rfl | hp | hp <;> rcases hq with rfl | hq | hq
      · intro _; rfl
      · intro h; exfalso; have := hX.1 q hq; dsimp only at h; omega
      · intro h; exfalso; have := hY.1 q hq; dsimp only at h; omega
      · intro h; exfalso; have := hX.1 p hp; dsimp only at h; omega
      · exact hX.2.1 p hp q hq
      · intro h; exfalso; have := hX.1 p hp; have := hY.1 q hq; omega
      · intro h; exfalso; have := hY.1 p hp; dsimp only at h; omega
      · intro h; exfalso; have := hY.1 p hp; have := hX.1 q hq; omega
      · exact hY.2.1 p hp q hq
    · intro p hp q hq
      simp only [mem_insert, mem_union] at hp hq
      rcases hp with rfl | hp | hp <;> rcases hq with rfl | hq | hq
      · dsimp only; omega
      · have := hX.1 q hq; dsimp only; omega
      · have := hY.1 q hq; dsimp only; omega
      · have := hX.1 p hp; dsimp only; omega
      · exact hX.2.2 p hp q hq
      · have := hX.1 p hp; have := hY.1 q hq; omega
      · have := hY.1 p hp; dsimp only; omega
      · have := hY.1 p hp; have := hX.1 q hq; omega
      · exact hY.2.2 p hp q hq
  · intro A hA
    simp only [mem_filter, mem_rna] at hA
    obtain ⟨hA, hac⟩ := hA
    simp only [mem_product, mem_rna]
    refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩
    · intro p hp
      simp only [mem_filter] at hp
      have h1 := hA.1 p hp.1
      have h2 := hA.2.1 p hp.1 (a, c) hac
      have : p.1 ≠ a := fun h => by
        have := h2 (Or.inl h)
        rw [this] at hp; exact absurd hp.2 (lt_irrefl _)
      omega
    · intro p hp q hq
      exact hA.2.1 p (mem_filter.1 hp).1 q (mem_filter.1 hq).1
    · intro p hp q hq
      exact hA.2.2 p (mem_filter.1 hp).1 q (mem_filter.1 hq).1
    · intro p hp
      simp only [mem_filter] at hp
      have h1 := hA.1 p hp.1
      omega
    · intro p hp q hq
      exact hA.2.1 p (mem_filter.1 hp).1 q (mem_filter.1 hq).1
    · intro p hp q hq
      exact hA.2.2 p (mem_filter.1 hp).1 q (mem_filter.1 hq).1
  · rintro ⟨X, Y⟩ hXY
    simp only [mem_product, mem_rna] at hXY
    obtain ⟨hX, hY⟩ := hXY
    simp only [Prod.mk.injEq]
    constructor
    · ext p
      simp only [mem_filter, mem_insert, mem_union]
      constructor
      · rintro ⟨rfl | hp | hp, hlt⟩
        · exact absurd hlt (lt_irrefl _)
        · exact hp
        · have := hY.1 p hp; omega
      · intro hp
        have := hX.1 p hp
        exact ⟨Or.inr (Or.inl hp), by omega⟩
    · ext p
      simp only [mem_filter, mem_insert, mem_union]
      constructor
      · rintro ⟨rfl | hp | hp, hlt⟩
        · dsimp only at hlt; omega
        · have := hX.1 p hp; omega
        · exact hp
      · intro hp
        have := hY.1 p hp
        exact ⟨Or.inr (Or.inr hp), by omega⟩
  · intro A hA
    simp only [mem_filter, mem_rna] at hA
    obtain ⟨hA, hac⟩ := hA
    ext p
    simp only [mem_insert, mem_union, mem_filter]
    constructor
    · rintro (rfl | hp | hp)
      · exact hac
      · exact hp.1
      · exact hp.1
    · intro hp
      rcases eq_or_ne p (a, c) with h | h
      · exact Or.inl h
      · right
        have hd := hA.2.1 p hp (a, c) hac
        have h1 : ¬ (p.1 = a ∨ p.1 = c ∨ p.2 = a ∨ p.2 = c) := fun h' => h (hd h')
        have h2 := hA.2.2 (a, c) hac p hp
        have h3 := hA.1 p hp
        dsimp only at h1 h2
        by_cases hpc : p.2 < c
        · exact Or.inl ⟨hp, hpc⟩
        · exact Or.inr ⟨hp, by omega⟩
  · intro _ _; rfl

theorem rna_sum (f : Finset (ℕ × ℕ) → ℚ) (a b : ℕ) :
    ∑ A ∈ rna a b, f A = ∑ A ∈ rna (a + 1) b, f A +
      ∑ c ∈ Ico (a + 2) b, ∑ X ∈ rna (a + 1) c, ∑ Y ∈ rna (c + 1) b,
        f (insert (a, c) (X ∪ Y)) := by
  have hsplit : rna a b = rna (a + 1) b ∪
      (Ico (a + 2) b).biUnion (fun c => (rna a b).filter (fun A => (a, c) ∈ A)) := by
    ext A
    simp only [mem_union, mem_biUnion, mem_filter, mem_Ico]
    constructor
    · intro hA
      by_cases h : ∃ p ∈ A, p.1 = a
      · obtain ⟨p, hp, hpa⟩ := h
        right
        have := (mem_rna.1 hA).1 p hp
        refine ⟨p.2, by omega, hA, ?_⟩
        have : p = (a, p.2) := Prod.ext hpa rfl
        rw [← this]; exact hp
      · left
        push Not at h
        have hA' := mem_rna.1 hA
        rw [mem_rna]
        refine ⟨fun p hp => ?_, hA'.2⟩
        have := hA'.1 p hp
        have := h p hp
        omega
    · rintro (h | ⟨c, _, h, _⟩)
      · have h' := mem_rna.1 h
        rw [mem_rna]
        refine ⟨fun p hp => ?_, h'.2⟩
        have := h'.1 p hp
        omega
      · exact h
  rw [hsplit, sum_union, sum_biUnion]
  · congr 1
    apply sum_congr rfl
    intro c hc
    rw [mem_Ico] at hc
    exact rna_fiber_sum f hc.1 hc.2
  · intro c _ c' _ hcc'
    simp only [Function.onFun]
    rw [disjoint_left]
    intro A h1 h2
    simp only [mem_filter] at h1 h2
    have := (mem_rna.1 h1.1).2.1 (a, c) h1.2 (a, c') h2.2 (Or.inl rfl)
    simp only [Prod.mk.injEq, true_and] at this
    exact hcc' this
  · rw [disjoint_left]
    intro A h1 h2
    simp only [mem_biUnion, mem_filter] at h2
    obtain ⟨c, _, _, hac⟩ := h2
    have := (mem_rna.1 h1).1 _ hac
    dsimp only at this
    omega



def rnaS (a b : ℕ) : ℚ := ∑ _A ∈ rna a b, (1 : ℚ)

def rnaW (a b : ℕ) : ℚ := ∑ A ∈ rna a b, ((b : ℚ) - a - A.card)

theorem rna_card_insert {a b c : ℕ} {X Y : Finset (ℕ × ℕ)} (hX : X ∈ rna (a + 1) c)
    (hY : Y ∈ rna (c + 1) b) : (insert (a, c) (X ∪ Y)).card = X.card + Y.card + 1 := by
  rw [mem_rna] at hX hY
  rw [card_insert_of_notMem, card_union_of_disjoint]
  · rw [disjoint_left]
    intro p h1 h2
    have := hX.1 p h1; have := hY.1 p h2; omega
  · simp only [mem_union, not_or]
    constructor
    · intro h; have := hX.1 _ h; dsimp only at this; omega
    · intro h; have := hY.1 _ h; dsimp only at this; omega

theorem rnaS_rec (a b : ℕ) : rnaS a b = rnaS (a + 1) b +
    ∑ c ∈ Ico (a + 2) b, rnaS (a + 1) c * rnaS (c + 1) b := by
  unfold rnaS
  rw [rna_sum]
  congr 1
  apply sum_congr rfl
  intro c _
  rw [sum_mul_sum]
  simp

theorem rnaW_rec (a b : ℕ) : rnaW a b = rnaW (a + 1) b + rnaS (a + 1) b +
    ∑ c ∈ Ico (a + 2) b, (rnaW (a + 1) c * rnaS (c + 1) b + rnaS (a + 1) c * rnaW (c + 1) b +
      rnaS (a + 1) c * rnaS (c + 1) b) := by
  unfold rnaS rnaW
  rw [rna_sum]
  congr 1
  · rw [← sum_add_distrib]
    apply sum_congr rfl
    intro A _
    push_cast; ring
  · apply sum_congr rfl
    intro c _
    rw [sum_mul_sum, sum_mul_sum, sum_mul_sum, ← sum_add_distrib, ← sum_add_distrib]
    apply sum_congr rfl
    intro X hX
    rw [← sum_add_distrib, ← sum_add_distrib]
    apply sum_congr rfl
    intro Y hY
    rw [rna_card_insert hX hY]
    push_cast; ring

def rs (n : ℕ) : ℚ := rnaS 0 n
def rw' (n : ℕ) : ℚ := rnaW 0 n

theorem sum_Ico_shift (g : ℕ → ℚ) (a m : ℕ) :
    ∑ c ∈ Ico (a + 2) (a + (m + 1)), g c = ∑ k ∈ range (m - 1), g (a + 2 + k) := by
  rw [sum_Ico_eq_sum_range, show a + (m + 1) - (a + 2) = m - 1 by omega]

theorem rnaS_len (a m : ℕ) : rnaS a (a + (m + 1)) = rnaS (a + 1) (a + (m + 1)) +
    ∑ k ∈ range (m - 1), rnaS (a + 1) (a + 2 + k) * rnaS (a + 2 + k + 1) (a + (m + 1)) := by
  rw [rnaS_rec, sum_Ico_shift (fun c => rnaS (a + 1) c * rnaS (c + 1) (a + (m + 1)))]

theorem rnaW_len (a m : ℕ) : rnaW a (a + (m + 1)) = rnaW (a + 1) (a + (m + 1)) +
    rnaS (a + 1) (a + (m + 1)) + ∑ k ∈ range (m - 1),
      (rnaW (a + 1) (a + 2 + k) * rnaS (a + 2 + k + 1) (a + (m + 1)) +
        rnaS (a + 1) (a + 2 + k) * rnaW (a + 2 + k + 1) (a + (m + 1)) +
        rnaS (a + 1) (a + 2 + k) * rnaS (a + 2 + k + 1) (a + (m + 1))) := by
  rw [rnaW_rec, sum_Ico_shift (fun c => rnaW (a + 1) c * rnaS (c + 1) (a + (m + 1)) +
    rnaS (a + 1) c * rnaW (c + 1) (a + (m + 1)) + rnaS (a + 1) c * rnaS (c + 1) (a + (m + 1)))]

theorem rna_trans (n : ℕ) : ∀ a, rnaS a (a + n) = rs n ∧ rnaW a (a + n) = rw' n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | m
    · intro a
      simp [rs, rw', rnaS, rnaW, rna_self]
    · have key : ∀ a, rnaS a (a + (m + 1)) =
            rs m + ∑ k ∈ range (m - 1), rs (k + 1) * rs (m - 2 - k) ∧
          rnaW a (a + (m + 1)) = rw' m + rs m + ∑ k ∈ range (m - 1),
            (rw' (k + 1) * rs (m - 2 - k) + rs (k + 1) * rw' (m - 2 - k) +
              rs (k + 1) * rs (m - 2 - k)) := by
        intro a
        have h1 := ih m (by omega) (a + 1)
        rw [show a + 1 + m = a + (m + 1) by omega] at h1
        have hin : ∀ k ∈ range (m - 1), rnaS (a + 1) (a + 2 + k) = rs (k + 1) ∧
            rnaW (a + 1) (a + 2 + k) = rw' (k + 1) := by
          intro k hk
          rw [mem_range] at hk
          have := ih (k + 1) (by omega) (a + 1)
          rwa [show a + 1 + (k + 1) = a + 2 + k by omega] at this
        have hout : ∀ k ∈ range (m - 1), rnaS (a + 2 + k + 1) (a + (m + 1)) = rs (m - 2 - k) ∧
            rnaW (a + 2 + k + 1) (a + (m + 1)) = rw' (m - 2 - k) := by
          intro k hk
          rw [mem_range] at hk
          have := ih (m - 2 - k) (by omega) (a + 2 + k + 1)
          rwa [show a + 2 + k + 1 + (m - 2 - k) = a + (m + 1) by omega] at this
        constructor
        · rw [rnaS_len, h1.1]
          congr 1
          apply sum_congr rfl
          intro k hk
          rw [(hin k hk).1, (hout k hk).1]
        · rw [rnaW_len, h1.1, h1.2]
          congr 1
          apply sum_congr rfl
          intro k hk
          rw [(hin k hk).1, (hout k hk).1, (hin k hk).2, (hout k hk).2]
      intro a
      have k0 := key 0
      simp only [zero_add] at k0
      refine ⟨(key a).1.trans ?_, (key a).2.trans ?_⟩
      · show _ = rnaS 0 (m + 1)
        rw [k0.1]
      · show _ = rnaW 0 (m + 1)
        rw [k0.2]

theorem rs_zero : rs 0 = 1 := by simp [rs, rnaS, rna_self]
theorem rw_zero : rw' 0 = 0 := by simp [rw', rnaW, rna_self]

theorem rs_succ (m : ℕ) : rs (m + 1) =
    rs m + ∑ k ∈ range (m - 1), rs (k + 1) * rs (m - 2 - k) := by
  have := (rna_trans (m + 1) 0).1
  rw [zero_add] at this
  rw [← this, ← (rna_trans m 1).1]
  have h := rnaS_len 0 m
  simp only [zero_add] at h
  rw [h, add_comm 1 m]
  congr 1
  apply sum_congr rfl
  intro k hk
  rw [mem_range] at hk
  have h1 := (rna_trans (k + 1) 1).1
  have h2 := (rna_trans (m - 2 - k) (2 + k + 1)).1
  rw [show 1 + (k + 1) = 2 + k by omega] at h1
  rw [show 2 + k + 1 + (m - 2 - k) = m + 1 by omega] at h2
  rw [h1, h2]

theorem rw_succ (m : ℕ) : rw' (m + 1) = rw' m + rs m + ∑ k ∈ range (m - 1),
    (rw' (k + 1) * rs (m - 2 - k) + rs (k + 1) * rw' (m - 2 - k) + rs (k + 1) * rs (m - 2 - k)) := by
  have := (rna_trans (m + 1) 0).2
  rw [zero_add] at this
  rw [← this, ← (rna_trans m 1).1, ← (rna_trans m 1).2]
  have h := rnaW_len 0 m
  simp only [zero_add] at h
  rw [h, add_comm 1 m]
  congr 1
  apply sum_congr rfl
  intro k hk
  rw [mem_range] at hk
  have h1 := (rna_trans (k + 1) 1)
  have h2 := (rna_trans (m - 2 - k) (2 + k + 1))
  rw [show 1 + (k + 1) = 2 + k by omega] at h1
  rw [show 2 + k + 1 + (m - 2 - k) = m + 1 by omega] at h2
  rw [h1.1, h1.2, h2.1, h2.2]

noncomputable def Sser : ℚ⟦X⟧ := PowerSeries.mk rs
noncomputable def Wser : ℚ⟦X⟧ := PowerSeries.mk rw'

theorem sum_ad_range (f : ℕ → ℕ → ℚ) (j : ℕ) :
    ∑ p ∈ antidiagonal j, f p.1 p.2 = ∑ k ∈ range (j + 1), f k (j - k) :=
  Nat.sum_antidiagonal_eq_sum_range_succ f j

theorem rs_one : rs 1 = 1 := by rw [rs_succ, rs_zero]; simp
theorem rs_two : rs 2 = 1 := by rw [rs_succ, rs_one]; simp
theorem rw_one : rw' 1 = 1 := by rw [rw_succ, rw_zero, rs_zero]; simp
theorem rw_two : rw' 2 = 2 := by rw [rw_succ, rw_one, rs_one]; norm_num

theorem Sser_eq : Sser = 1 + X * Sser + X * (X * ((Sser - 1) * Sser)) := by
  ext n
  rcases n with _ | _ | _ | j
  · simp [Sser, rs_zero]
  · rw [map_add, map_add, coeff_succ_X_mul, coeff_succ_X_mul, coeff_zero_X_mul]
    simp [Sser, rs_zero, rs_one]
  · rw [map_add, map_add, coeff_succ_X_mul, coeff_succ_X_mul, coeff_succ_X_mul]
    simp [Sser, rs_zero, rs_one, rs_two]
  · rw [map_add, map_add, coeff_succ_X_mul, coeff_succ_X_mul, coeff_succ_X_mul, coeff_mul,
      Nat.sum_antidiagonal_succ]
    simp only [Sser, coeff_mk, map_sub, coeff_one, rs_zero, sub_self, zero_mul, zero_add,
      Nat.add_one_ne_zero, ite_false, sub_zero, ite_true]
    rw [rs_succ, sum_ad_range (fun a b => rs (a + 1) * rs b),
      show j + 1 + 1 - 1 = j + 1 by omega]
    congr 1

theorem Wser_eq : Wser = X * Wser + X * Sser +
    X * (X * (Wser * Sser + (Sser - 1) * Wser + (Sser - 1) * Sser)) := by
  ext n
  rcases n with _ | _ | _ | j
  · simp [Wser, rw_zero]
  · rw [map_add, map_add, coeff_succ_X_mul, coeff_succ_X_mul, coeff_succ_X_mul]
    simp [Wser, Sser, rs_zero, rw_zero, rw_one]
  · rw [map_add, map_add, coeff_succ_X_mul, coeff_succ_X_mul, coeff_succ_X_mul]
    simp [Wser, Sser, rs_zero, rs_one, rw_zero, rw_one, rw_two]
    norm_num
  · rw [map_add, map_add, coeff_succ_X_mul, coeff_succ_X_mul, coeff_succ_X_mul, coeff_succ_X_mul,
      map_add, map_add,
      coeff_mul, coeff_mul, coeff_mul, Nat.sum_antidiagonal_succ, Nat.sum_antidiagonal_succ,
      Nat.sum_antidiagonal_succ]
    simp only [Sser, Wser, coeff_mk, map_sub, coeff_one, rs_zero, rw_zero, sub_self, zero_mul,
      zero_add, Nat.add_one_ne_zero, ite_false, sub_zero, ite_true]
    rw [rw_succ, sum_ad_range (fun a b => rw' (a + 1) * rs b),
      sum_ad_range (fun a b => rs (a + 1) * rw' b), sum_ad_range (fun a b => rs (a + 1) * rs b),
      show j + 1 + 1 - 1 = j + 1 by omega, ← sum_add_distrib, ← sum_add_distrib]
    congr 1

theorem Wser_mul_R : Wser * (1 - X + X ^ 2 - 2 * X ^ 2 * Sser) = Sser - 1 := by
  linear_combination Wser_eq - Sser_eq

/-! ### Words over {U, H, D} avoiding the factor UD

`Wd pos init n h u`: number of such words of length n ending at height h whose last
letter is U iff `u`; `pos` restricts to words whose prefixes stay at height ≥ 0. -/

def Wd (pos : Bool) (init : ℤ → Bool → ℚ) : ℕ → ℤ → Bool → ℚ
  | 0, h, u => init h u
  | n + 1, h, true =>
      if pos = true ∧ h < 0 then 0 else Wd pos init n (h - 1) true + Wd pos init n (h - 1) false
  | n + 1, h, false =>
      if pos = true ∧ h < 0 then 0
      else Wd pos init n h true + Wd pos init n h false + Wd pos init n (h + 1) false

def i0 (h : ℤ) (u : Bool) : ℚ := if h = 0 ∧ u = false then 1 else 0
def i1 (h : ℤ) (u : Bool) : ℚ := if h = 0 ∧ u = true then 1 else 0

theorem Wd_st (p : Bool) (i : ℤ → Bool → ℚ) (n : ℕ) (h : ℤ) : Wd p i (n + 1) h true =
    if p = true ∧ h < 0 then 0 else Wd p i n (h - 1) true + Wd p i n (h - 1) false := rfl
theorem Wd_sf (p : Bool) (i : ℤ → Bool → ℚ) (n : ℕ) (h : ℤ) : Wd p i (n + 1) h false =
    if p = true ∧ h < 0 then 0
    else Wd p i n h true + Wd p i n h false + Wd p i n (h + 1) false := rfl

def cw : ℕ → ℤ → Bool → ℚ := Wd false i0
def ew : ℕ → ℤ → Bool → ℚ := Wd true i0
def ehat : ℕ → ℤ → Bool → ℚ := Wd true i1

theorem cw_zero (h : ℤ) (u : Bool) : cw 0 h u = i0 h u := rfl
theorem cw_true (n : ℕ) (h : ℤ) : cw (n + 1) h true = cw n (h - 1) true + cw n (h - 1) false := by
  simp [cw, Wd]
theorem cw_false (n : ℕ) (h : ℤ) :
    cw (n + 1) h false = cw n h true + cw n h false + cw n (h + 1) false := by
  simp [cw, Wd]

theorem Wd_true_pos (init) (n : ℕ) (h : ℤ) (hh : 0 ≤ h) :
    Wd true init (n + 1) h true = Wd true init n (h - 1) true + Wd true init n (h - 1) false := by
  simp [Wd, not_lt.2 hh]
theorem Wd_false_pos (init) (n : ℕ) (h : ℤ) (hh : 0 ≤ h) :
    Wd true init (n + 1) h false =
      Wd true init n h true + Wd true init n h false + Wd true init n (h + 1) false := by
  simp [Wd, not_lt.2 hh]
theorem Wd_neg_succ (init) (n : ℕ) (h : ℤ) (u : Bool) (hh : h < 0) :
    Wd true init (n + 1) h u = 0 := by
  cases u <;> simp [Wd, hh]

theorem Wd_neg (init : ℤ → Bool → ℚ) (hi : ∀ h u, h < 0 → init h u = 0) :
    ∀ n h u, h < 0 → Wd true init n h u = 0 := by
  intro n h u hh
  cases n with
  | zero => exact hi h u hh
  | succ n => exact Wd_neg_succ init n h u hh

theorem ew_neg (n : ℕ) (h : ℤ) (u : Bool) (hh : h < 0) : ew n h u = 0 :=
  Wd_neg i0 (fun h u hh => by simp [i0]; omega) n h u hh
theorem ehat_neg (n : ℕ) (h : ℤ) (u : Bool) (hh : h < 0) : ehat n h u = 0 :=
  Wd_neg i1 (fun h u hh => by simp [i1]; omega) n h u hh

theorem ew_zero_true (n : ℕ) : ew n 0 true = 0 := by
  cases n with
  | zero => simp [ew, Wd, i0]
  | succ n =>
    show Wd true i0 (n + 1) 0 true = 0
    rw [Wd_true_pos _ _ _ le_rfl]
    rw [show ((0 : ℤ) - 1) = -1 by norm_num]
    simp only [show Wd true i0 = ew from rfl, ew_neg n (-1) true (by norm_num),
      ew_neg n (-1) false (by norm_num), add_zero]

theorem ehat_eq : ∀ n h u, ehat (n + 1) h u = ew (n + 1) h u := by
  intro n
  induction n with
  | zero =>
    intro h u
    cases u
    · simp only [ehat, ew, Wd, i0, i1]; split_ifs <;> simp_all; omega
    · simp only [ehat, ew, Wd, i0, i1]; split_ifs <;> norm_num
  | succ n ih =>
    intro h u
    simp only [ehat, ew] at ih ⊢
    cases u
    · rw [Wd_sf true i1 (n + 1), Wd_sf true i0 (n + 1)]; simp only [ih]
    · rw [Wd_st true i1 (n + 1), Wd_st true i0 (n + 1)]; simp only [ih]

/-- Last-visit decomposition at heights `≥ 1`. -/
theorem lastvisit (Xf : ℕ → ℤ → Bool → ℚ) (h0 : ∀ h u, 1 ≤ h → Xf 0 h u = 0)
    (ht : ∀ n h, 1 ≤ h → Xf (n + 1) h true = Xf n (h - 1) true + Xf n (h - 1) false)
    (hf : ∀ n h, 1 ≤ h → Xf (n + 1) h false = Xf n h true + Xf n h false + Xf n (h + 1) false) :
    ∀ n h u, 1 ≤ h → Xf (n + 1) h u =
      ∑ p ∈ antidiagonal n, (Xf p.1 0 true + Xf p.1 0 false) * ehat p.2 (h - 1) u := by
  intro n
  induction n with
  | zero =>
    intro h u hh
    simp only [Finset.Nat.antidiagonal_zero, sum_singleton]
    cases u
    · rw [hf 0 h hh, h0 h _ hh, h0 h _ hh, h0 (h + 1) _ (by omega)]
      simp [ehat, Wd, i1]
    · rw [ht 0 h hh]
      rcases eq_or_lt_of_le hh with e | e
      · subst e; simp [ehat, Wd, i1]
      · rw [h0 _ _ (by omega), h0 _ _ (by omega)]
        simp [ehat, Wd, i1]
        intro h'; omega
  | succ n ih =>
    intro h u hh
    rw [Nat.sum_antidiagonal_succ']
    cases u
    · rw [hf (n + 1) h hh, ih h true hh, ih h false hh, ih (h + 1) false (by omega)]
      have e0 : ehat 0 (h - 1) false = 0 := by simp [ehat, Wd, i1]
      rw [e0, mul_zero, zero_add]
      simp only [ehat] at *
      simp only [Wd_false_pos i1 _ (h - 1) (by omega), sub_add_cancel, add_sub_cancel_right,
        mul_add, sum_add_distrib]
    · rw [ht (n + 1) h hh]
      rcases eq_or_lt_of_le hh with e | e
      · subst e
        have : ∀ k, ehat (k + 1) ((1 : ℤ) - 1) true = 0 := by
          intro k
          simp only [ehat, Wd_true_pos i1 k _ (by norm_num : (0 : ℤ) ≤ 1 - 1)]
          rw [show ((1 : ℤ) - 1 - 1) = -1 by norm_num]
          simp only [show Wd true i1 = ehat from rfl, ehat_neg k (-1) _ (by norm_num), add_zero]
        simp only [this, mul_zero, sum_const_zero, add_zero]
        simp [ehat, Wd, i1]
      · rw [ih (h - 1) true (by omega), ih (h - 1) false (by omega)]
        have e0 : ehat 0 (h - 1) true = 0 := by simp [ehat, Wd, i1]; omega
        rw [e0, mul_zero, zero_add]
        simp only [ehat] at *
        simp only [Wd_true_pos i1 _ (h - 1) (by omega), mul_add, sum_add_distrib]

/-- First-visit decomposition: split a word at its first visit to height -1. -/
theorem firstvisit : ∀ n h u, cw (n + 1) h u = ew (n + 1) h u +
    ∑ p ∈ antidiagonal n, (ew p.1 0 true + ew p.1 0 false) * cw p.2 (h + 1) u := by
  intro n
  induction n with
  | zero =>
    intro h u
    simp only [Finset.Nat.antidiagonal_zero, sum_singleton]
    cases u <;> simp only [cw, ew, Wd, i0] <;> split_ifs <;> simp_all <;> omega
  | succ n ih =>
    intro h u
    rw [Nat.sum_antidiagonal_succ']
    cases u
    · rw [cw_false, ih h true, ih h false, ih (h + 1) false, cw_zero]
      simp only [cw_false, mul_add, sum_add_distrib]
      rcases lt_or_ge h 0 with hh | hh
      · rw [show ew (n + 1 + 1) h false = 0 from ew_neg _ _ _ hh, ew_neg _ h true hh,
          ew_neg _ h false hh]
        rcases eq_or_lt_of_le (show h + 1 ≤ 0 by omega) with e | e
        · have : h = -1 := by omega
          subst this
          simp only [show (-1 : ℤ) + 1 = 0 by norm_num, ew_zero_true, i0]
          simp
          ring
        · have hi : i0 (h + 1) false = 0 := by simp [i0]; omega
          rw [ew_neg _ (h + 1) false e, hi]
          ring
      · have hi : i0 (h + 1) false = 0 := by simp [i0]; omega
        rw [hi]
        simp only [ew, Wd_false_pos i0 _ h hh]
        ring
    · rw [cw_true, ih (h - 1) true, ih (h - 1) false, cw_zero]
      simp only [cw_true, mul_add, sum_add_distrib, sub_add_cancel, add_sub_cancel_right]
      simp only [i0, Bool.true_eq_false, and_false, ite_false, mul_zero, zero_add]
      rcases lt_or_ge h 0 with hh | hh
      · rw [show ew (n + 1 + 1) h true = 0 from ew_neg _ _ _ hh, ew_neg _ (h - 1) true (by omega),
          ew_neg _ (h - 1) false (by omega)]
        ring
      · simp only [ew, Wd_true_pos i0 _ h hh]
        ring

def Fw (n : ℕ) : ℚ := cw n 0 true + cw n 0 false
def C1w (n : ℕ) : ℚ := cw n 1 true + cw n 1 false
def sw (n : ℕ) : ℚ := ew n 0 false

theorem sw_zero : sw 0 = 1 := by simp [sw, ew, Wd, i0]

theorem Fw_succ (n : ℕ) : Fw (n + 1) = sw (n + 1) + ∑ p ∈ antidiagonal n, sw p.1 * C1w p.2 := by
  unfold Fw
  rw [firstvisit n 0 true, firstvisit n 0 false, ew_zero_true]
  simp only [ew_zero_true, zero_add, sw, C1w, mul_add, sum_add_distrib]
  ring

theorem ehat_tot (k : ℕ) : ehat k 0 true + ehat k 0 false = sw k := by
  cases k with
  | zero => simp [ehat, sw, ew, Wd, i0, i1]
  | succ k => rw [ehat_eq, ehat_eq, ew_zero_true, zero_add]; rfl

theorem ehat_f (k : ℕ) : ehat k 0 false = sw k - if k = 0 then 1 else 0 := by
  cases k with
  | zero => simp [ehat, sw, ew, Wd, i0, i1]
  | succ k => rw [ehat_eq]; simp [sw]

theorem C1w_succ (n : ℕ) : C1w (n + 1) = ∑ p ∈ antidiagonal n, Fw p.1 * sw p.2 := by
  have hl := lastvisit cw (fun h u hh => by simp [cw, Wd, i0]; omega)
    (fun n h _ => cw_true n h) (fun n h _ => cw_false n h)
  unfold C1w
  rw [hl n 1 true le_rfl, hl n 1 false le_rfl, ← sum_add_distrib]
  apply sum_congr rfl
  intro p _
  rw [← mul_add, sub_self, ehat_tot]
  rfl

theorem ew1_succ (n : ℕ) :
    ew (n + 1) 1 false = ∑ p ∈ antidiagonal n, sw p.1 * ehat p.2 0 false := by
  have hl := lastvisit ew (fun h u hh => by simp [ew, Wd, i0]; omega)
    (fun n h hh => Wd_true_pos i0 n h (by omega)) (fun n h hh => Wd_false_pos i0 n h (by omega))
  rw [hl n 1 false le_rfl]
  apply sum_congr rfl
  intro p _
  rw [ew_zero_true, zero_add, sub_self]
  rfl

theorem sw_succ (n : ℕ) : sw (n + 1) = sw n + ew n 1 false := by
  unfold sw
  rw [show ew (n + 1) 0 false = _ from Wd_false_pos i0 n 0 le_rfl]
  simp only [show Wd true i0 = ew from rfl, ew_zero_true, zero_add]

noncomputable def S2 : ℚ⟦X⟧ := PowerSeries.mk sw
noncomputable def Fser : ℚ⟦X⟧ := PowerSeries.mk Fw
noncomputable def C1ser : ℚ⟦X⟧ := PowerSeries.mk C1w
noncomputable def E1ser : ℚ⟦X⟧ := PowerSeries.mk (fun n => ew n 1 false)

theorem E1ser_eq : E1ser = X * (S2 * (S2 - 1)) := by
  ext n
  cases n with
  | zero => simp [E1ser, ew, Wd, i0]
  | succ n =>
    rw [coeff_succ_X_mul, coeff_mul, E1ser, coeff_mk, ew1_succ]
    apply sum_congr rfl
    intro p _
    simp [S2, ehat_f, coeff_one]

theorem S2_eq : S2 = 1 + X * S2 + X * (X * (S2 * (S2 - 1))) := by
  rw [← E1ser_eq]
  ext n
  cases n with
  | zero => simp [S2, sw_zero]
  | succ n =>
    rw [map_add, map_add, coeff_succ_X_mul, coeff_succ_X_mul, coeff_one]
    simp [S2, E1ser, sw_succ]

theorem C1ser_eq : C1ser = X * (Fser * S2) := by
  ext n
  cases n with
  | zero => simp [C1ser, C1w, cw, Wd, i0]
  | succ n =>
    rw [coeff_succ_X_mul, coeff_mul, C1ser, coeff_mk, C1w_succ]
    simp [Fser, S2]

theorem Fser_eq : Fser = S2 + X * (S2 * C1ser) := by
  ext n
  cases n with
  | zero => simp [Fser, S2, Fw, sw, cw, ew, Wd, i0]
  | succ n =>
    rw [map_add, coeff_succ_X_mul, coeff_mul, Fser, coeff_mk, Fw_succ]
    simp [C1ser, S2]

theorem const_ne_zero {f : ℚ⟦X⟧} (hf : constantCoeff f = 1) : f ≠ 0 := by
  intro h; rw [h, map_zero] at hf; exact zero_ne_one hf

theorem S2_eq_Sser : S2 = Sser := by
  have h : (Sser - S2) * (1 - X - X * (X * (Sser + S2 - 1))) = 0 := by
    linear_combination Sser_eq - S2_eq
  rcases mul_eq_zero.1 h with h | h
  · exact (sub_eq_zero.1 h).symm
  · exfalso
    have := congrArg constantCoeff h
    simp at this

theorem Sser_const : constantCoeff Sser = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply, Sser, coeff_mk, rs_zero]

noncomputable def Rser : ℚ⟦X⟧ := 1 - X + X ^ 2 - 2 * X ^ 2 * Sser

theorem Fser_mul_R : Fser * Rser = 1 := by
  have hF := Fser_eq
  rw [C1ser_eq, S2_eq_Sser] at hF
  have h : Sser * (Fser * Rser - 1) = 0 := by
    unfold Rser
    linear_combination Fser * Sser_eq + hF
  rcases mul_eq_zero.1 h with h | h
  · exact absurd h (const_ne_zero Sser_const)
  · exact sub_eq_zero.1 h

theorem Rser_const : constantCoeff Rser = 1 := by
  simp [Rser]

theorem Rser_sq : Rser ^ 2 = 1 - 2 * X - X ^ 2 - 2 * X ^ 3 + X ^ 4 := by
  unfold Rser
  linear_combination (-4 * X ^ 2) * Sser_eq

/-! ### Fences and crowns -/

def fenceLE (x y : ℕ) : Prop := x = y ∨ (y % 2 = 1 ∧ (x + 1 = y ∨ x = y + 1))

theorem fenceLE_order : (∀ x, fenceLE x x) ∧ (∀ x y, fenceLE x y → fenceLE y x → x = y) ∧
    (∀ x y z, fenceLE x y → fenceLE y z → fenceLE x z) := by
  unfold fenceLE
  refine ⟨fun x => Or.inl rfl, fun x y h1 h2 => by omega, fun x y z h1 h2 => by omega⟩

def IsFenceIdeal (m : ℕ) (I : Finset ℕ) : Prop :=
  ∀ y ∈ I, ∀ x ∈ range (2 * m), fenceLE x y → x ∈ I

instance (m : ℕ) : DecidablePred (IsFenceIdeal m) := fun I => by
  unfold IsFenceIdeal fenceLE; infer_instance

def fenceIdeals (m : ℕ) : Finset (Finset ℕ) :=
  (range (2 * m)).powerset.filter (IsFenceIdeal m)

theorem mem_fence {m : ℕ} {I : Finset ℕ} : I ∈ fenceIdeals m ↔
    (∀ y ∈ I, y < 2 * m) ∧ ∀ y ∈ I, ∀ x, x < 2 * m → fenceLE x y → x ∈ I := by
  unfold fenceIdeals
  rw [mem_filter, mem_powerset]
  unfold IsFenceIdeal
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun y hy => mem_range.1 (h1 hy), fun y hy x hx => h2 y hy x (mem_range.2 hx)⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun y hy => mem_range.2 (h1 y hy), fun y hy x hx => h2 y hy x (mem_range.1 hx)⟩

theorem fenceIdeals_zero : fenceIdeals 0 = {∅} := by
  ext I
  rw [mem_fence, mem_singleton]
  constructor
  · rintro ⟨h1, _⟩
    rw [eq_empty_iff_forall_notMem]
    intro y hy; have := h1 y hy; omega
  · rintro rfl; simp

theorem fence_sum (f : Finset ℕ → ℚ) (m : ℕ) :
    ∑ I ∈ fenceIdeals (m + 1), f I = ∑ J ∈ fenceIdeals m,
      ((if (m ≠ 0 ∧ 2 * m - 1 ∈ J) then 0 else f J) + f (insert (2 * m) J) +
        f (insert (2 * m + 1) (insert (2 * m) J))) := by
  set A := fenceIdeals (m + 1)
  have e1 : ∑ I ∈ A.filter (fun I => 2 * m ∉ I), f I =
      ∑ J ∈ fenceIdeals m, (if (m ≠ 0 ∧ 2 * m - 1 ∈ J) then 0 else f J) := by
    have : A.filter (fun I => 2 * m ∉ I) =
        (fenceIdeals m).filter (fun J => ¬ (m ≠ 0 ∧ 2 * m - 1 ∈ J)) := by
      ext I
      simp only [A, mem_filter, mem_fence]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩
        have h4 : 2 * m + 1 ∉ I := fun h =>
          h3 (h2 _ h (2 * m) (by omega) (by unfold fenceLE; omega))
        refine ⟨⟨fun y hy => ?_, fun y hy x hx hle => h2 y hy x (by omega) hle⟩, ?_⟩
        · have := h1 y hy
          have : y ≠ 2 * m := fun e => h3 (e ▸ hy)
          have : y ≠ 2 * m + 1 := fun e => h4 (e ▸ hy)
          omega
        · rintro ⟨hm, h⟩
          exact h3 (h2 _ h (2 * m) (by omega) (by unfold fenceLE; omega))
      · rintro ⟨⟨h1, h2⟩, h3⟩
        refine ⟨⟨fun y hy => by have := h1 y hy; omega, fun y hy x hx hle => ?_⟩,
          fun h => by have := h1 _ h; omega⟩
        by_cases hx' : x < 2 * m
        · exact h2 y hy x hx' hle
        · exfalso
          have := h1 y hy
          unfold fenceLE at hle
          have hy' : y = 2 * m - 1 := by omega
          exact h3 ⟨by omega, hy' ▸ hy⟩
    rw [this, sum_filter]
    apply sum_congr rfl
    intro J _
    by_cases h : m ≠ 0 ∧ 2 * m - 1 ∈ J <;> simp [h]
  have e2 : ∑ I ∈ (A.filter (fun I => ¬ 2 * m ∉ I)).filter (fun I => 2 * m + 1 ∉ I), f I =
      ∑ J ∈ fenceIdeals m, f (insert (2 * m) J) := by
    apply sum_nbij' (fun I => I.erase (2 * m)) (fun J => insert (2 * m) J)
    · intro I hI
      simp only [A, mem_filter, mem_fence, not_not] at hI
      obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hI
      rw [mem_fence]
      refine ⟨fun y hy => ?_, fun y hy x hx hle => ?_⟩
      · rw [mem_erase] at hy
        have := h1 y hy.2
        have : y ≠ 2 * m + 1 := fun e => h4 (e ▸ hy.2)
        omega
      · rw [mem_erase] at hy ⊢
        exact ⟨by omega, h2 y hy.2 x (by omega) hle⟩
    · intro J hJ
      rw [mem_fence] at hJ
      obtain ⟨h1, h2⟩ := hJ
      simp only [A, mem_filter, mem_fence, not_not, mem_insert, true_or, and_true]
      refine ⟨⟨fun y hy => ?_, fun y hy x hx hle => ?_⟩, ?_⟩
      · rcases hy with rfl | hy
        · omega
        · have := h1 y hy; omega
      · rcases hy with rfl | hy
        · unfold fenceLE at hle; left; omega
        · by_cases hx' : x < 2 * m
          · exact Or.inr (h2 y hy x hx' hle)
          · have := h1 y hy
            unfold fenceLE at hle
            left; omega
      · rintro (h | h)
        · omega
        · have := h1 _ h; omega
    · intro I hI
      simp only [A, mem_filter, not_not] at hI
      exact insert_erase hI.1.2
    · intro J hJ
      rw [mem_fence] at hJ
      exact erase_insert (fun h => by have := hJ.1 _ h; omega)
    · intro I hI
      simp only [A, mem_filter, not_not] at hI
      rw [insert_erase hI.1.2]
  have e3 : ∑ I ∈ (A.filter (fun I => ¬ 2 * m ∉ I)).filter (fun I => ¬ 2 * m + 1 ∉ I), f I =
      ∑ J ∈ fenceIdeals m, f (insert (2 * m + 1) (insert (2 * m) J)) := by
    apply sum_nbij' (fun I => (I.erase (2 * m + 1)).erase (2 * m))
      (fun J => insert (2 * m + 1) (insert (2 * m) J))
    · intro I hI
      simp only [A, mem_filter, mem_fence, not_not] at hI
      obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hI
      rw [mem_fence]
      refine ⟨fun y hy => ?_, fun y hy x hx hle => ?_⟩
      · simp only [mem_erase] at hy
        have := h1 y hy.2.2
        omega
      · simp only [mem_erase] at hy ⊢
        exact ⟨by omega, by omega, h2 y hy.2.2 x (by omega) hle⟩
    · intro J hJ
      rw [mem_fence] at hJ
      obtain ⟨h1, h2⟩ := hJ
      simp only [A, mem_filter, mem_fence, not_not, mem_insert, true_or, or_true, and_true]
      refine ⟨fun y hy => ?_, fun y hy x hx hle => ?_⟩
      · rcases hy with rfl | rfl | hy
        · omega
        · omega
        · have := h1 y hy; omega
      · rcases hy with rfl | rfl | hy
        · unfold fenceLE at hle; omega
        · unfold fenceLE at hle; omega
        · by_cases hx' : x < 2 * m
          · exact Or.inr (Or.inr (h2 y hy x hx' hle))
          · have := h1 y hy
            unfold fenceLE at hle
            omega
    · intro I hI
      simp only [A, mem_filter, not_not] at hI
      rw [insert_erase (mem_erase.2 ⟨by omega, hI.1.2⟩), insert_erase hI.2]
    · intro J hJ
      rw [mem_fence] at hJ
      rw [erase_insert, erase_insert]
      · exact fun h => by have := hJ.1 _ h; omega
      · simp only [mem_insert, not_or]
        exact ⟨by omega, fun h => by have := hJ.1 _ h; omega⟩
    · intro I hI
      simp only [A, mem_filter, not_not] at hI
      rw [insert_erase (mem_erase.2 ⟨by omega, hI.1.2⟩), insert_erase hI.2]
  rw [← sum_filter_add_sum_filter_not A (fun I => 2 * m ∉ I),
    ← sum_filter_add_sum_filter_not (A.filter (fun I => ¬ 2 * m ∉ I)) (fun I => 2 * m + 1 ∉ I),
    e1, e2, e3, sum_add_distrib, sum_add_distrib]
  ring

def Gp (P : Finset ℕ → Prop) [DecidablePred P] (m : ℕ) (h : ℤ) (u : Bool) : ℚ :=
  ∑ I ∈ fenceIdeals m,
    if ((I.card : ℤ) - m = h ∧ decide (m ≠ 0 ∧ 2 * m - 1 ∈ I) = u ∧ P I) then 1 else 0

theorem Gp_succ (P : Finset ℕ → Prop) [DecidablePred P] (m : ℕ)
    (hP : ∀ J ∈ fenceIdeals m, (P (insert (2 * m) J) ↔ P J) ∧
      (P (insert (2 * m + 1) (insert (2 * m) J)) ↔ P J)) (h : ℤ) :
    Gp P (m + 1) h true = Gp P m (h - 1) true + Gp P m (h - 1) false ∧
    Gp P (m + 1) h false = Gp P m h true + Gp P m h false + Gp P m (h + 1) false := by
  unfold Gp
  rw [fence_sum, fence_sum, ← sum_add_distrib, ← sum_add_distrib, ← sum_add_distrib]
  constructor
  all_goals
    apply sum_congr rfl
    intro J hJ
    have hJ' := (mem_fence.1 hJ).1
    have n1 : 2 * m ∉ J := fun h => by have := hJ' _ h; omega
    have n2 : 2 * m + 1 ∉ J := fun h => by have := hJ' _ h; omega
    have hc1 : ((insert (2 * m) J).card : ℤ) = J.card + 1 := by
      rw [card_insert_of_notMem n1]; push_cast; ring
    have hc2 : ((insert (2 * m + 1) (insert (2 * m) J)).card : ℤ) = J.card + 2 := by
      rw [card_insert_of_notMem, card_insert_of_notMem n1]
      · push_cast; ring
      · simp only [mem_insert, not_or]; exact ⟨by omega, n2⟩
    have hl0 : decide (m + 1 ≠ 0 ∧ 2 * (m + 1) - 1 ∈ J) = false := by
      simp only [decide_eq_false_iff_not, not_and]
      intro _ h; exact n2 (by rwa [show 2 * (m + 1) - 1 = 2 * m + 1 by omega] at h)
    have hl1 : decide (m + 1 ≠ 0 ∧ 2 * (m + 1) - 1 ∈ insert (2 * m) J) = false := by
      simp only [decide_eq_false_iff_not, not_and, mem_insert, not_or]
      intro _
      rw [show 2 * (m + 1) - 1 = 2 * m + 1 by omega]
      exact ⟨by omega, n2⟩
    have hl2 : decide (m + 1 ≠ 0 ∧ 2 * (m + 1) - 1 ∈ insert (2 * m + 1) (insert (2 * m) J))
        = true := by
      simp only [decide_eq_true_eq, mem_insert]
      exact ⟨by omega, Or.inl (by omega)⟩
    rw [hc1, hc2, hl0, hl1, hl2]
    simp only [(hP J hJ).1, (hP J hJ).2]
    push_cast
    by_cases hL : m ≠ 0 ∧ 2 * m - 1 ∈ J <;> by_cases hp : P J <;>
      simp only [hL, hp, not_false_eq_true, decide_eq_true_eq, decide_eq_false_iff_not,
        and_false, and_true, ite_false, add_zero, zero_add] <;>
      (try split_ifs) <;> first | (norm_num; done) | (exfalso; omega)

theorem Gp_zero (P : Finset ℕ → Prop) [DecidablePred P] (h : ℤ) (u : Bool) :
    Gp P 0 h u = if (0 = h ∧ false = u ∧ P ∅) then 1 else 0 := by
  rw [Gp, fenceIdeals_zero, sum_singleton]
  simp

theorem Gp_true_eq (m : ℕ) : ∀ h u, Gp (fun _ => True) m h u = cw m h u := by
  induction m with
  | zero =>
    intro h u
    rw [Gp_zero, cw_zero, i0]
    cases u
    · simp
      split_ifs <;> first | rfl | (exfalso; omega)
    · simp [eq_comm]
  | succ m ih =>
    intro h u
    have hs := Gp_succ (fun _ => True) m (fun _ _ => ⟨Iff.rfl, Iff.rfl⟩) h
    cases u
    · rw [hs.2, cw_false, ih, ih, ih]
    · rw [hs.1, cw_true, ih, ih]

theorem Gp_zero_eq (m : ℕ) : ∀ h u, Gp (fun I => 0 ∉ I) (m + 1) h u = cw m (h + 1) u := by
  induction m with
  | zero =>
    intro h u
    unfold Gp
    rw [fence_sum, fenceIdeals_zero, sum_singleton, cw_zero, i0]
    cases u
    · simp
      split_ifs <;> first | rfl | (exfalso; omega)
    · simp
  | succ m ih =>
    intro h u
    have hs := Gp_succ (fun I => 0 ∉ I) (m + 1) (fun J _ => by
      simp only [mem_insert, not_or]
      constructor
      · constructor
        · exact fun h => h.2
        · exact fun h => ⟨by omega, h⟩
      · constructor
        · exact fun h => h.2.2
        · exact fun h => ⟨by omega, by omega, h⟩) h
    cases u
    · rw [hs.2, cw_false, ih, ih, ih]
    · rw [hs.1, cw_true, ih, ih, sub_add_cancel, add_sub_cancel_right]

def fenceCount (n : ℕ) : ℕ := ((fenceIdeals n).filter (fun I => I.card = n)).card

theorem fenceCount_eq (n : ℕ) : (fenceCount n : ℚ) = Fw n := by
  rw [fenceCount, natCast_card_filter, Fw, ← Gp_true_eq, ← Gp_true_eq, Gp, Gp, ← sum_add_distrib]
  apply sum_congr rfl
  intro I _
  have hcz : ((I.card : ℤ) - n = 0) ↔ I.card = n := by omega
  simp only [hcz]
  by_cases hc : I.card = n <;> by_cases hL : (n ≠ 0 ∧ 2 * n - 1 ∈ I) <;> simp [hc, hL]

def crownLE (m x y : ℕ) : Prop := x = y ∨ (y % 2 = 1 ∧ (x + 1 = y ∨ x = (y + 1) % (2 * m)))

def IsCrownIdeal (m : ℕ) (I : Finset ℕ) : Prop :=
  ∀ y ∈ I, ∀ x ∈ range (2 * m), crownLE m x y → x ∈ I

instance (m : ℕ) : DecidablePred (IsCrownIdeal m) := fun I => by
  unfold IsCrownIdeal crownLE; infer_instance

def crownIdeals (m : ℕ) : Finset (Finset ℕ) :=
  (range (2 * m)).powerset.filter (IsCrownIdeal m)

def crownCount (n : ℕ) : ℕ := ((crownIdeals n).filter (fun I => I.card = n)).card

theorem crownLE_iff {m x y : ℕ} (hx : x < 2 * m) (hy : y < 2 * m) :
    crownLE m x y ↔ (fenceLE x y ∨ (y + 1 = 2 * m ∧ x = 0)) := by
  unfold crownLE fenceLE
  rcases Nat.lt_or_ge (y + 1) (2 * m) with h | h
  · rw [Nat.mod_eq_of_lt h]
    constructor <;> intro <;> omega
  · rw [show y + 1 = 2 * m by omega, Nat.mod_self]
    constructor <;> intro <;> omega

theorem crownIdeals_eq (m : ℕ) (hm : 1 ≤ m) :
    crownIdeals m = (fenceIdeals m).filter (fun I => 2 * m - 1 ∈ I → 0 ∈ I) := by
  ext I
  rw [mem_filter, mem_fence]
  unfold crownIdeals
  rw [mem_filter, mem_powerset]
  unfold IsCrownIdeal
  constructor
  · rintro ⟨h1, h2⟩
    have h1' : ∀ y ∈ I, y < 2 * m := fun y hy => mem_range.1 (h1 hy)
    refine ⟨⟨h1', fun y hy x hx hle => h2 y hy x (mem_range.2 hx)
      ((crownLE_iff hx (h1' y hy)).2 (Or.inl hle))⟩, fun h => ?_⟩
    exact h2 _ h 0 (mem_range.2 (by omega)) ((crownLE_iff (by omega) (by omega)).2
      (Or.inr ⟨by omega, rfl⟩))
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨fun y hy => mem_range.2 (h1 y hy), fun y hy x hx hle => ?_⟩
    rw [mem_range] at hx
    rcases (crownLE_iff hx (h1 y hy)).1 hle with h | ⟨h, rfl⟩
    · exact h2 y hy x hx h
    · exact h3 (by rwa [show 2 * m - 1 = y by omega])

theorem crownCount_eq (m : ℕ) (hm : 2 ≤ m) : (crownCount m : ℚ) = Fw m - Fw (m - 2) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
  have hz := Gp_zero_eq (k + 1) 0 true
  rw [zero_add, cw_true, sub_self] at hz
  rw [show k + 2 - 2 = k by omega, crownCount, crownIdeals_eq _ (by omega), filter_filter,
    natCast_card_filter, Fw, Fw, ← Gp_true_eq, ← Gp_true_eq, ← hz, Gp, Gp, Gp,
    ← sum_add_distrib, ← sum_sub_distrib]
  apply sum_congr rfl
  intro I _
  have hcz : ((I.card : ℤ) - (k + 2 : ℕ) = 0) ↔ I.card = k + 2 := by omega
  simp only [show k + 1 + 1 = k + 2 from rfl, hcz]
  by_cases h1 : 2 * (k + 2) - 1 ∈ I <;> by_cases h2 : 0 ∈ I <;> by_cases hc : I.card = k + 2 <;>
    simp [h1, h2, hc]

def rnaBlockCount (n : ℕ) : ℕ :=
  ∑ A ∈ rna 0 n, (A.card + ((range n).filter (fun i => ∀ p ∈ A, p.1 ≠ i ∧ p.2 ≠ i)).card)

theorem rna_singles {n : ℕ} {A : Finset (ℕ × ℕ)} (hA : A ∈ rna 0 n) :
    ((range n).filter (fun i => ∀ p ∈ A, p.1 ≠ i ∧ p.2 ≠ i)).card + 2 * A.card = n := by
  have hA' := mem_rna.1 hA
  have hE : (A.biUnion (fun p => ({p.1, p.2} : Finset ℕ))).card = 2 * A.card := by
    rw [card_biUnion]
    · rw [sum_congr rfl (fun p hp => card_pair (by have := hA'.1 p hp; omega)), sum_const,
        smul_eq_mul, mul_comm]
    · intro p hp q hq hpq
      simp only [Function.onFun]
      rw [disjoint_left]
      intro i hi hi'
      simp only [mem_insert, mem_singleton] at hi hi'
      exact hpq (hA'.2.1 p hp q hq (by omega))
  have hf : (range n).filter (fun i => ¬ ∀ p ∈ A, p.1 ≠ i ∧ p.2 ≠ i) =
      A.biUnion (fun p => ({p.1, p.2} : Finset ℕ)) := by
    ext i
    rw [mem_filter, mem_biUnion, mem_range]
    constructor
    · rintro ⟨_, h⟩
      push Not at h
      obtain ⟨p, hp, h⟩ := h
      refine ⟨p, hp, ?_⟩
      rw [mem_insert, mem_singleton]
      by_cases e : p.1 = i
      · exact Or.inl e.symm
      · exact Or.inr (h e).symm
    · rintro ⟨p, hp, hi⟩
      rw [mem_insert, mem_singleton] at hi
      have := hA'.1 p hp
      refine ⟨by omega, fun h => ?_⟩
      have := h p hp
      omega
  rw [← hE, ← hf, card_filter_add_card_filter_not, card_range]

theorem rnaBlockCount_eq (n : ℕ) : (rnaBlockCount n : ℚ) = rw' n := by
  rw [rnaBlockCount, rw', rnaW]
  push_cast
  apply sum_congr rfl
  intro A hA
  have h := rna_singles hA
  have h2 : (((range n).filter (fun i => ∀ p ∈ A, p.1 ≠ i ∧ p.2 ≠ i)).card : ℚ) +
      2 * (A.card : ℚ) = n := by exact_mod_cast h
  linarith

theorem Rser_inv : Rser⁻¹ = Fser := by
  have h : Rser * Rser⁻¹ = 1 := PowerSeries.mul_inv_cancel Rser (by rw [Rser_const]; norm_num)
  calc Rser⁻¹ = (Fser * Rser) * Rser⁻¹ := by rw [Fser_mul_R, one_mul]
    _ = Fser := by rw [mul_assoc, h, mul_one]

theorem blocks_key : X * (X * (Wser + Wser)) = Fser - X * Fser - X * (X * Fser) - 1 := by
  have h1 := Wser_mul_R
  have h2 := Fser_mul_R
  unfold Rser at h2
  linear_combination (-1 - 2 * X ^ 2 * Wser) * h2 + (2 * X ^ 2 * Fser) * h1

/-! ### The printed generating functions describe the combinatorial sequences -/

theorem Rser_unique (R : ℚ⟦X⟧) (h1 : R ^ 2 = 1 - 2 * X - X ^ 2 - 2 * X ^ 3 + X ^ 4)
    (h2 : constantCoeff R = 1) : R = Rser := by
  have h : (R - Rser) * (R + Rser) = 0 := by linear_combination h1 - Rser_sq
  rcases mul_eq_zero.1 h with h | h
  · exact sub_eq_zero.1 h
  · exfalso
    have := congrArg constantCoeff h
    rw [map_add, h2, Rser_const, map_zero] at this
    norm_num at this

theorem fence_gf (n : ℕ) : (fenceCount n : ℚ) = a051286 Rser n := by
  rw [a051286, Rser_inv, fenceCount_eq, Fser, coeff_mk]

theorem crown_gf (n : ℕ) (hn : 2 ≤ n) : (crownCount n : ℚ) = a051292 Rser n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  have h : Rser * Fser = 1 := by rw [mul_comm]; exact Fser_mul_R
  have e : (1 - X ^ 2 + Rser) * Rser⁻¹ = Fser - X * (X * Fser) + 1 := by
    rw [Rser_inv]; linear_combination h
  rw [a051292, e, crownCount_eq _ (by omega), show k + 2 - 2 = k by omega,
    show k + 2 = (k + 1) + 1 from rfl, map_add, map_sub, coeff_succ_X_mul, coeff_succ_X_mul,
    coeff_one]
  simp [Fser]

theorem blocks_gf (n : ℕ) : (rnaBlockCount n : ℚ) = a110320 Rser n := by
  have e : (1 - X - X ^ 2) * Rser⁻¹ - 1 = X * (X * (Wser + Wser)) := by
    rw [Rser_inv, blocks_key]; ring
  rw [a110320, e, show n + 2 = (n + 1) + 1 from rfl, coeff_succ_X_mul, coeff_succ_X_mul, map_add,
    Wser, coeff_mk, rnaBlockCount_eq]
  ring

/-- **Main theorem** (McGarvey's conjecture for A110320), with all three sequences defined
combinatorially: the number of blocks over all RNA secondary structures on `n` nodes equals
`(A051292(n+2) - A051286(n+1))/2`. -/
theorem A110320_main (n : ℕ) :
    (rnaBlockCount n : ℚ) = ((crownCount (n + 2) : ℚ) - fenceCount (n + 1)) / 2 := by
  rw [blocks_gf, crown_gf _ (by omega), fence_gf]
  exact A110320_gf_identity Rser Rser_const n

/-- The same identity in `ℕ`, without division. -/
theorem A110320_main_nat (n : ℕ) : 2 * rnaBlockCount n + fenceCount (n + 1) = crownCount (n + 2) := by
  have h := A110320_main n
  have h' : ((2 * rnaBlockCount n + fenceCount (n + 1) : ℕ) : ℚ) = crownCount (n + 2) := by
    push_cast; linarith
  exact_mod_cast h'
