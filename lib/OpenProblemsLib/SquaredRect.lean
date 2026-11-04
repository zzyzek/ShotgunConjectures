import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# Squared rectangles: an exact tiling from a kernel-checkable certificate

A square `⟨s, x, y⟩` (side `s`, lower-left corner `(x, y)`, natural numbers) is the closed set
`[x, x+s] × [y, y+s] ⊆ ℝ²` (`Sq.toSet`); its interior is the open box (`Sq.inner`).
`IsTiling W H l`: every side is positive, the union of the squares of `l` is exactly
`[0, W] × [0, H]`, and the interiors are pairwise disjoint.

`tilingCheck W H l : Bool` checks: W, H > 0, positive sides, every square inside the rectangle,
pairwise apart (interiors disjoint), and for every unit column `[i, i+1]`, `i < W`, a chain of
squares spanning that column whose y-intervals cover `[0, H)` bottom to top (`colOK`).
`tiling_of_check : tilingCheck W H l = true → IsTiling W H l`: the columns cover
`[0, W) × [0, H)`; the finite union of closed squares is closed, so it covers the closure
`[0, W] × [0, H]`.
-/

namespace OpenProblemsLib.SquaredRect

/-- An axis-parallel square with side `s` and lower-left corner `(x, y)`. -/
structure Sq where
  s : ℕ
  x : ℕ
  y : ℕ
  deriving DecidableEq

/-- The closed square in `ℝ × ℝ`. -/
def Sq.toSet (q : Sq) : Set (ℝ × ℝ) :=
  Set.Icc (q.x : ℝ) (q.x + q.s) ×ˢ Set.Icc (q.y : ℝ) (q.y + q.s)

/-- The open square (interior). -/
def Sq.inner (q : Sq) : Set (ℝ × ℝ) :=
  Set.Ioo (q.x : ℝ) (q.x + q.s) ×ˢ Set.Ioo (q.y : ℝ) (q.y + q.s)

/-- The squares of `l` tile the rectangle `[0, W] × [0, H]` exactly. -/
def IsTiling (W H : ℕ) (l : List Sq) : Prop :=
  (∀ q ∈ l, 0 < q.s) ∧
    (⋃ q ∈ l, q.toSet) = Set.Icc (0 : ℝ) W ×ˢ Set.Icc (0 : ℝ) H ∧
    l.Pairwise (fun p q => Disjoint p.inner q.inner)

def inside (W H : ℕ) (q : Sq) : Bool := q.x + q.s ≤ W && q.y + q.s ≤ H

def apart (p q : Sq) : Bool :=
  p.x + p.s ≤ q.x || q.x + q.s ≤ p.x || p.y + p.s ≤ q.y || q.y + q.s ≤ p.y

def pairwiseApart : List Sq → Bool
  | [] => true
  | q :: qs => qs.all (apart q) && pairwiseApart qs

/-- `q` spans the unit column `[i, i+1]`. -/
def spans (q : Sq) (i : ℕ) : Bool := q.x ≤ i && i < q.x + q.s

/-- From height `cur` up to `H`, column `i` is covered by a chain of at most `f` squares. -/
def colOK (l : List Sq) (i H : ℕ) : ℕ → ℕ → Bool
  | 0, cur => H ≤ cur
  | f + 1, cur => H ≤ cur ||
      l.any (fun q => spans q i && q.y ≤ cur && cur < q.y + q.s && colOK l i H f (q.y + q.s))

def tilingCheck (W H : ℕ) (l : List Sq) : Bool :=
  0 < W && 0 < H && l.all (fun q => 0 < q.s && inside W H q) && pairwiseApart l &&
    (List.range W).all (fun i => colOK l i H l.length 0)

theorem apart_disjoint (p q : Sq) (h : apart p q = true) : Disjoint p.inner q.inner := by
  rw [Set.disjoint_left]
  rintro ⟨u, v⟩ ⟨⟨hu1, hu2⟩, ⟨hv1, hv2⟩⟩ ⟨⟨hu3, hu4⟩, ⟨hv3, hv4⟩⟩
  simp only [apart, Bool.or_eq_true, decide_eq_true_eq] at h
  rcases h with ((h | h) | h) | h
  · have : ((p.x + p.s : ℕ) : ℝ) ≤ q.x := by exact_mod_cast h
    push_cast at this; linarith
  · have : ((q.x + q.s : ℕ) : ℝ) ≤ p.x := by exact_mod_cast h
    push_cast at this; linarith
  · have : ((p.y + p.s : ℕ) : ℝ) ≤ q.y := by exact_mod_cast h
    push_cast at this; linarith
  · have : ((q.y + q.s : ℕ) : ℝ) ≤ p.y := by exact_mod_cast h
    push_cast at this; linarith

theorem pairwise_of_check : ∀ l : List Sq, pairwiseApart l = true →
    l.Pairwise (fun p q => Disjoint p.inner q.inner)
  | [], _ => List.Pairwise.nil
  | q :: qs, h => by
    simp only [pairwiseApart, Bool.and_eq_true, List.all_eq_true] at h
    exact List.Pairwise.cons (fun r hr => apart_disjoint q r (h.1 r hr))
      (pairwise_of_check qs h.2)

theorem colOK_spec (l : List Sq) (i H : ℕ) : ∀ f cur, colOK l i H f cur = true →
    ∀ v : ℝ, (cur : ℝ) ≤ v → v < H →
      ∃ q ∈ l, spans q i = true ∧ (q.y : ℝ) ≤ v ∧ v < q.y + q.s
  | 0, cur, h, v, hv1, hv2 => by
    simp only [colOK, decide_eq_true_eq] at h
    have : (H : ℝ) ≤ cur := by exact_mod_cast h
    linarith
  | f + 1, cur, h, v, hv1, hv2 => by
    simp only [colOK, Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true,
      Bool.and_eq_true] at h
    rcases h with h | ⟨q, hq, ⟨⟨hs, h1⟩, h2⟩, hrec⟩
    · have : (H : ℝ) ≤ cur := by exact_mod_cast h
      linarith
    · by_cases hv : v < q.y + q.s
      · refine ⟨q, hq, hs, ?_, hv⟩
        have : (q.y : ℝ) ≤ cur := by exact_mod_cast h1
        linarith
      · push Not at hv
        exact colOK_spec l i H f _ hrec v (by push_cast; linarith) hv2

theorem tiling_of_check (W H : ℕ) (l : List Sq) (h : tilingCheck W H l = true) :
    IsTiling W H l := by
  simp only [tilingCheck, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq,
    List.mem_range] at h
  obtain ⟨⟨⟨⟨hW, hH⟩, hpos⟩, hpw⟩, hcol⟩ := h
  refine ⟨fun q hq => (hpos q hq).1, ?_, pairwise_of_check l hpw⟩
  apply Set.Subset.antisymm
  · intro z hz
    simp only [Set.mem_iUnion] at hz
    obtain ⟨q, hq, ⟨hu1, hu2⟩, ⟨hv1, hv2⟩⟩ := hz
    have hin := (hpos q hq).2
    simp only [inside, Bool.and_eq_true, decide_eq_true_eq] at hin
    have hx : ((q.x + q.s : ℕ) : ℝ) ≤ W := by exact_mod_cast hin.1
    have hy : ((q.y + q.s : ℕ) : ℝ) ≤ H := by exact_mod_cast hin.2
    push_cast at hx hy
    have : (0 : ℝ) ≤ q.x := Nat.cast_nonneg _
    have : (0 : ℝ) ≤ q.y := Nat.cast_nonneg _
    exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  · -- the union is closed and contains [0, W) × [0, H)
    have hclosed : IsClosed (⋃ q ∈ l, q.toSet) := by
      apply Set.Finite.isClosed_biUnion (List.finite_toSet l)
      intro q _
      exact isClosed_Icc.prod isClosed_Icc
    have hsub : Set.Ico (0 : ℝ) W ×ˢ Set.Ico (0 : ℝ) H ⊆ ⋃ q ∈ l, q.toSet := by
      rintro ⟨u, v⟩ ⟨⟨hu0, huW⟩, ⟨hv0, hvH⟩⟩
      set i := ⌊u⌋₊ with hi
      have hiW : i < W := (Nat.floor_lt hu0).mpr huW
      have hiu : (i : ℝ) ≤ u := Nat.floor_le hu0
      have hui : u < i + 1 := Nat.lt_floor_add_one u
      obtain ⟨q, hq, hs, hy1, hy2⟩ := colOK_spec l i H _ 0 (hcol i hiW) v (by simpa using hv0) hvH
      simp only [spans, Bool.and_eq_true, decide_eq_true_eq] at hs
      have h1 : (q.x : ℝ) ≤ i := by exact_mod_cast hs.1
      have h2 : ((i + 1 : ℕ) : ℝ) ≤ q.x + q.s := by exact_mod_cast hs.2
      push_cast at h2
      simp only [Set.mem_iUnion]
      exact ⟨q, hq, ⟨by linarith, by linarith⟩, ⟨hy1, hy2.le⟩⟩
    have hW' : (0 : ℝ) ≠ W := (show (0 : ℝ) < W by exact_mod_cast hW).ne
    have hH' : (0 : ℝ) ≠ H := (show (0 : ℝ) < H by exact_mod_cast hH).ne
    rw [← closure_Ico hW', ← closure_Ico hH', ← closure_prod_eq]
    exact closure_minimal hsub hclosed

end OpenProblemsLib.SquaredRect
