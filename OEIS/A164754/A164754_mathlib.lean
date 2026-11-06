import Mathlib

/-
OEIS A164754 (offset 2): number of n x 2 arrays with entries 1..4, each value's
cells connected, 1, 2, 3, 4 in the upper left, upper right, lower left and lower
right corners, and no cell with more than 2 neighbours of its own value.
Conjecture (entry, empirical): a(n) = 4n^2 - 11n + 5 for n >= 3.

Definitions.  Rows are `Fin n`, columns `Bool` (false = left).  Colours
0, 1, 2, 3 stand for the values 1, 2, 3, 4.  `Adj` is 4-adjacency, `Step f c`
a step between adjacent cells of colour c, connectivity is
`Relation.ReflTransGen (Step f c)`, and "more than 2 neighbours of its own
value" is three pairwise distinct adjacent cells of that value (`Valid.deg`).
`a n` is the number of `f : Fin n × Bool → Fin 4` with `Valid f`.

Main theorem.
* `A164754_formula`: (a n : ℤ) = 4 n^2 - 11 n + 5 for every n ≥ 3.

Route.
* `valid_iff_model`: `Valid f ↔ Model f`, where `Model` says: corners; each
  value fills an interval of rows in each column (`column_interval`, via
  `row_hit`); a value in both columns has a shared row (`meet_of_valid`);
  every shared row is an end of both intervals.  `a_eq_model` follows.
* `monoL`, `mono`: in a `Model` array the left column reads 1, 2, 4, 3 and the
  right column 2, 1, 3, 4 from top to bottom (some blocks possibly empty);
  `mir`/`model_mir` is the left-right mirror used for the right column.
* `thr`, `tau`, `build`: an array is coded by its six block boundaries
  (`build_tau`); `cross1`..`cross4` and `thr_basic` give the constraints `Cn`
  (`tau_mem`); conversely every tuple in `T n` builds a `Model` array
  (`model_build`) with that code (`tau_build`).  So `card_model`: the number
  of `Model` arrays is `(T n).card`.
* `card_T_eq_D`, `card_D`, `card_T`: `T n` is in bijection with nine
  parametrised families, of sizes (n-1)^2, four of C(n-1,2), two of C(n-2,2)
  and two of n-3 (`pairs_card`, `square_card`, `line_card`).

Not checked in this file: agreement of `a` with the OEIS data terms
(certificate/brute.py computes a(2..7) from the same definition).
-/

namespace A164754

variable {n : ℕ}

abbrev Cell (n : ℕ) := Fin n × Bool

/-- Grid adjacency in an `n × 2` array: same row other column, or same column adjacent rows. -/
def Adj (x y : Cell n) : Prop :=
  (x.1 = y.1 ∧ x.2 ≠ y.2) ∨ (x.2 = y.2 ∧ (x.1.val + 1 = y.1.val ∨ y.1.val + 1 = x.1.val))

/-- One step of a path of cells of colour `c`. -/
def Step (f : Cell n → Fin 4) (c : Fin 4) (x y : Cell n) : Prop :=
  Adj x y ∧ f x = c ∧ f y = c

/-- Counted arrays.  Colours 0, 1, 2, 3 stand for the values 1, 2, 3, 4; column `false` is the left one. -/
structure Valid (f : Cell n → Fin 4) : Prop where
  top : ∀ x : Cell n, x.1.val = 0 → f x = (if x.2 then 1 else 0)
  bot : ∀ x : Cell n, x.1.val + 1 = n → f x = (if x.2 then 3 else 2)
  conn : ∀ x y : Cell n, f x = f y → Relation.ReflTransGen (Step f (f x)) x y
  deg : ∀ x y₁ y₂ y₃ : Cell n, Adj x y₁ → Adj x y₂ → Adj x y₃ →
    y₁ ≠ y₂ → y₁ ≠ y₃ → y₂ ≠ y₃ → f y₁ = f x → f y₂ = f x → f y₃ = f x → False

/-- The interval characterisation (steps 1-2 of the README). -/
structure Model (f : Cell n → Fin 4) : Prop where
  top : ∀ x : Cell n, x.1.val = 0 → f x = (if x.2 then 1 else 0)
  bot : ∀ x : Cell n, x.1.val + 1 = n → f x = (if x.2 then 3 else 2)
  interval : ∀ (j : Bool) (i k r : Fin n), f (i, j) = f (k, j) → i.val < r.val → r.val < k.val →
    f (r, j) = f (i, j)
  meet : ∀ i k : Fin n, f (i, false) = f (k, true) →
    ∃ s : Fin n, f (s, false) = f (i, false) ∧ f (s, true) = f (i, false)
  ends : ∀ (s u v : Fin n) (j : Bool), f (s, false) = f (s, true) → u.val + 1 = s.val →
    s.val + 1 = v.val → f (u, j) = f (s, j) → f (v, j) = f (s, j) → False

/-- OEIS A164754: the number of counted `n × 2` arrays. -/
noncomputable def a (n : ℕ) : ℕ :=
  open Classical in (Finset.univ.filter (fun f : Cell n → Fin 4 => Valid f)).card

end A164754

open A164754

theorem adj_symm {x y : Cell n} (h : Adj x y) : Adj y x := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨h1.symm, Ne.symm h2⟩
  · exact Or.inr ⟨h1.symm, h2.symm⟩

theorem step_symm {f : Cell n → Fin 4} {c : Fin 4} {x y : Cell n} (h : Step f c x y) :
    Step f c y x :=
  ⟨adj_symm h.1, h.2.2, h.2.1⟩

theorem rtg_symm {f : Cell n → Fin 4} {c : Fin 4} {x y : Cell n}
    (h : Relation.ReflTransGen (Step f c) x y) : Relation.ReflTransGen (Step f c) y x :=
  by
    induction h with
    | refl => exact .refl
    | tail _ hab ih => exact Relation.ReflTransGen.head (step_symm hab) ih

theorem adj_row {x y : Cell n} (h : Adj x y) : y.1.val ≤ x.1.val + 1 ∧ x.1.val ≤ y.1.val + 1 := by
  rcases h with ⟨h1, _⟩ | ⟨_, h2 | h2⟩
  · rw [h1]; omega
  · omega
  · omega

/-- A path of colour `c` meets every row between its ends in a cell of colour `c`. -/
theorem row_hit {f : Cell n → Fin 4} {c : Fin 4} {x y : Cell n} (hx : f x = c)
    (h : Relation.ReflTransGen (Step f c) x y) :
    ∀ r (hr : r < n), x.1.val ≤ r → r ≤ y.1.val → ∃ j, f (⟨r, hr⟩, j) = c := by
  induction h with
  | refl =>
    intro r hr h1 h2
    refine ⟨x.2, ?_⟩
    have : (⟨r, hr⟩ : Fin n) = x.1 := Fin.ext (by simp only; omega)
    rw [this]; exact hx
  | @tail z y _ hzy ih =>
    intro r hr h1 h2
    by_cases hz : r ≤ z.1.val
    · exact ih r hr h1 hz
    · have := adj_row hzy.1
      refine ⟨y.2, ?_⟩
      have : (⟨r, hr⟩ : Fin n) = y.1 := Fin.ext (by simp; omega)
      rw [this]; exact hzy.2.2

theorem row_hit' {f : Cell n → Fin 4} {c : Fin 4} {x y : Cell n} (hx : f x = c)
    (hy : f y = c) (h : Relation.ReflTransGen (Step f c) x y) :
    ∀ r (hr : r < n), (x.1.val ≤ r ∧ r ≤ y.1.val) ∨ (y.1.val ≤ r ∧ r ≤ x.1.val) →
      ∃ j, f (⟨r, hr⟩, j) = c := by
  intro r hr h'
  rcases h' with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact row_hit hx h r hr h1 h2
  · exact row_hit hy (rtg_symm h) r hr h1 h2

/-- Every colour occupies a cell in the top row or the bottom row. -/
theorem corner_of {f : Cell n → Fin 4} (hv : Valid f) (hn : 0 < n) (d : Fin 4) :
    ∃ x : Cell n, f x = d ∧ (x.1.val = 0 ∨ x.1.val + 1 = n) := by
  fin_cases d
  · exact ⟨(⟨0, hn⟩, false), by simpa using hv.top (⟨0, hn⟩, false) rfl, Or.inl rfl⟩
  · exact ⟨(⟨0, hn⟩, true), by simpa using hv.top (⟨0, hn⟩, true) rfl, Or.inl rfl⟩
  · exact ⟨(⟨n - 1, by omega⟩, false),
      by simpa using hv.bot (⟨n - 1, by omega⟩, false) (by simp; omega), Or.inr (by simp; omega)⟩
  · exact ⟨(⟨n - 1, by omega⟩, true),
      by simpa using hv.bot (⟨n - 1, by omega⟩, true) (by simp; omega), Or.inr (by simp; omega)⟩

/-- Step 1: each colour fills an interval of rows in each column. -/
theorem column_interval {f : Cell n → Fin 4} (hv : Valid f) (j : Bool) (i k r : Fin n)
    (hi : f (i, j) = f (k, j)) (hir : i.val < r.val) (hrk : r.val < k.val) :
    f (r, j) = f (i, j) := by
  by_contra hne
  set c := f (i, j) with hc
  set d := f (r, j) with hd
  have hpath := hv.conn (i, j) (k, j) hi
  -- rows strictly between `i` and `k` whose cell in column `j` is not `c` have a `c` in the other column
  have other : ∀ s : Fin n, i.val < s.val → s.val < k.val → f (s, j) ≠ c → f (s, !j) = c := by
    intro s h1 h2 h3
    obtain ⟨j', hj'⟩ := row_hit rfl hpath s.val s.isLt (by simp; omega) (by simp; omega)
    have hs : (⟨s.val, s.isLt⟩ : Fin n) = s := rfl
    rw [hs] at hj'
    cases j <;> cases j' <;> simp_all
  -- `d`-paths from `(r, j)` stay in column `j` strictly between rows `i` and `k`
  have enclosed : ∀ z, Relation.ReflTransGen (Step f d) (r, j) z →
      z.2 = j ∧ i.val < z.1.val ∧ z.1.val < k.val := by
    intro z hz
    induction hz with
    | refl => exact ⟨rfl, hir, hrk⟩
    | @tail z y _ hzy ih =>
      obtain ⟨hz2, hz1, hz3⟩ := ih
      obtain ⟨hadj, hfz, hfy⟩ := hzy
      rcases hadj with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exfalso
        have hzc : f (z.1, j) ≠ c := by
          have : (z.1, j) = z := by ext <;> simp [hz2]
          rw [this, hfz]; exact hne
        have := other z.1 hz1 hz3 hzc
        have hy2 : y.2 = !j := by
          rw [← hz2]; revert h2; generalize y.2 = b; generalize z.2 = b'
          cases b <;> cases b' <;> simp
        have hy : y = (z.1, !j) := by
          ext
          · simp [h1]
          · simp [hy2]
        rw [← hy, hfy] at this
        exact hne this
      · refine ⟨by rw [← h1, hz2], ?_, ?_⟩
        · by_contra hlt
          have hyi : y = (i, j) := by
            ext
            · simp; omega
            · simp [← h1, hz2]
          rw [hyi] at hfy; exact hne hfy.symm
        · by_contra hlt
          have hyk : y = (k, j) := by
            ext
            · simp; omega
            · simp [← h1, hz2]
          rw [hyk, ← hi] at hfy; exact hne hfy.symm
  obtain ⟨x, hx, hx2⟩ := corner_of hv (by omega) d
  have := enclosed x (hv.conn (r, j) x hx.symm)
  rcases hx2 with h | h <;> omega


/-- Step 2(a): a colour with cells in both columns has a row where both cells carry it. -/
theorem meet_of_valid {f : Cell n → Fin 4} (hv : Valid f) (i k : Fin n)
    (h : f (i, false) = f (k, true)) :
    ∃ s : Fin n, f (s, false) = f (i, false) ∧ f (s, true) = f (i, false) := by
  have hp := hv.conn (i, false) (k, true) h
  have key : ∀ z, Relation.ReflTransGen (Step f (f (i, false))) (i, false) z →
      z.2 = false ∨ ∃ s : Fin n, f (s, false) = f (i, false) ∧ f (s, true) = f (i, false) := by
    intro z hz
    induction hz with
    | refl => exact Or.inl rfl
    | @tail z y _ hzy ih =>
      rcases ih with hz2 | hex
      · obtain ⟨hadj, hfz, hfy⟩ := hzy
        cases hy2 : y.2
        · exact Or.inl rfl
        · rcases hadj with ⟨h1, _⟩ | ⟨h1, _⟩
          · refine Or.inr ⟨z.1, ?_, ?_⟩
            · have : (z.1, false) = z := by ext <;> simp [hz2]
              rw [this]; exact hfz
            · have : (z.1, true) = y := by ext <;> simp [h1, hy2]
              rw [this]; exact hfy
          · rw [hz2, hy2] at h1; exact absurd h1 (by decide)
      · exact Or.inr hex
  rcases key (k, true) hp with h2 | hex
  · simp at h2
  · exact hex

theorem model_of_valid {f : Cell n → Fin 4} (hv : Valid f) : Model f where
  top := hv.top
  bot := hv.bot
  interval := fun j i k r h1 h2 h3 => column_interval hv j i k r h1 h2 h3
  meet := meet_of_valid hv
  ends := by
    intro s u v j hs hu hv' hfu hfv
    have hh : f (s, !j) = f (s, j) := by cases j <;> simp [hs]
    refine hv.deg (s, j) (s, !j) (u, j) (v, j) ?_ ?_ ?_ ?_ ?_ ?_ hh hfu hfv
    · exact Or.inl ⟨rfl, by cases j <;> simp⟩
    · exact Or.inr ⟨rfl, Or.inr hu⟩
    · exact Or.inr ⟨rfl, Or.inl hv'⟩
    · intro h; cases j <;> simp at h
    · intro h; cases j <;> simp at h
    · intro h; have := congrArg (fun z => z.1.val) h; simp at this; omega

/-- Cells of colour `c` filling a column interval are joined by a path of colour `c`. -/
theorem vert_path {f : Cell n → Fin 4} (hm : Model f) (j : Bool) (i k : Fin n)
    (h : f (i, j) = f (k, j)) : Relation.ReflTransGen (Step f (f (i, j))) (i, j) (k, j) := by
  -- walk from `i` towards `k` one row at a time
  have walk : ∀ d, ∀ i k : Fin n, f (i, j) = f (k, j) → k.val = i.val + d →
      Relation.ReflTransGen (Step f (f (i, j))) (i, j) (k, j) := by
    intro d
    induction d with
    | zero =>
      intro i k _ hk
      have : k = i := Fin.ext (by omega)
      rw [this]
    | succ d ih =>
      intro i k hik hk
      have hm1 : i.val + d < n := by omega
      set m : Fin n := ⟨i.val + d, hm1⟩
      have hfm : f (m, j) = f (i, j) := by
        rcases Nat.eq_zero_or_pos d with hd | hd
        · have : m = i := Fin.ext (by simp [m, hd])
          rw [this]
        · exact hm.interval j i k m hik (by simp [m]; omega) (by simp [m]; omega)
      have h1 := ih i m hfm.symm rfl
      refine h1.tail ⟨Or.inr ⟨rfl, Or.inl (by simp [m]; omega)⟩, hfm, hik.symm⟩
  rcases Nat.lt_or_ge i.val k.val with hlt | hge
  · exact walk (k.val - i.val) i k h (by omega)
  · have := walk (i.val - k.val) k i h.symm (by omega)
    rw [← h] at this
    exact rtg_symm this

theorem adj_cases {x y : Cell n} (h : Adj x y) :
    y = (x.1, !x.2) ∨ (y.2 = x.2 ∧ y.1.val + 1 = x.1.val) ∨ (y.2 = x.2 ∧ x.1.val + 1 = y.1.val) := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2 | h2⟩
  · left
    refine Prod.ext h1.symm ?_
    · revert h2; generalize x.2 = b; generalize y.2 = b'; cases b <;> cases b' <;> simp
  · right; right; exact ⟨h1.symm, h2⟩
  · right; left; exact ⟨h1.symm, h2⟩

theorem valid_of_model {f : Cell n → Fin 4} (hm : Model f) : Valid f where
  top := hm.top
  bot := hm.bot
  conn := by
    intro x y hxy
    obtain ⟨xi, xj⟩ := x
    obtain ⟨yi, yj⟩ := y
    cases xj <;> cases yj
    · exact vert_path hm false xi yi hxy
    · obtain ⟨s, hs1, hs2⟩ := hm.meet xi yi hxy
      have p1 := vert_path hm false xi s hs1.symm
      have p3 := vert_path hm true s yi (by rw [hs2, hxy])
      rw [hs2] at p3
      have st : Step f (f (xi, false)) (s, false) (s, true) := ⟨Or.inl ⟨rfl, by simp⟩, hs1, hs2⟩
      exact Relation.ReflTransGen.trans (Relation.ReflTransGen.tail p1 st) p3
    · obtain ⟨s, hs1, hs2⟩ := hm.meet yi xi hxy.symm
      have p1 := vert_path hm true xi s (by rw [hs2, hxy])
      have p3 := vert_path hm false s yi hs1
      rw [show f (s, false) = f (xi, true) from hs1.trans hxy.symm] at p3
      have st : Step f (f (xi, true)) (s, true) (s, false) :=
        ⟨Or.inl ⟨rfl, by simp⟩, hs2.trans hxy.symm, hs1.trans hxy.symm⟩
      exact Relation.ReflTransGen.trans (Relation.ReflTransGen.tail p1 st) p3
    · exact vert_path hm true xi yi hxy
  deg := by
    intro x y₁ y₂ y₃ h1 h2 h3 h12 h13 h23 f1 f2 f3
    -- the helper: a horizontal neighbour, one above and one below, all of the colour of `x`
    have help : ∀ y z w : Cell n, y = (x.1, !x.2) → (z.2 = x.2 ∧ z.1.val + 1 = x.1.val) →
        (w.2 = x.2 ∧ x.1.val + 1 = w.1.val) → f y = f x → f z = f x → f w = f x → False := by
      intro y z w hy hz hw fy fz fw
      obtain ⟨xi, xj⟩ := x
      obtain ⟨zi, zj⟩ := z
      obtain ⟨wi, wj⟩ := w
      simp only at hy hz hw fz fw
      obtain ⟨hzj, hz⟩ := hz
      obtain ⟨hwj, hw⟩ := hw
      rw [hzj] at fz
      rw [hwj] at fw
      rw [hy] at fy
      refine hm.ends xi zi wi xj ?_ hz hw fz fw
      cases xj <;> simp only [Bool.not_false, Bool.not_true] at fy <;> first | exact fy | exact fy.symm
    have same : ∀ y z : Cell n, (y.2 = x.2 ∧ z.2 = x.2 ∧ y.1.val = z.1.val) → y = z := by
      intro y z ⟨h1, h2, h3⟩
      ext
      · exact h3
      · rw [h1, h2]
    rcases adj_cases h1 with a1 | a1 | a1 <;> rcases adj_cases h2 with a2 | a2 | a2 <;>
      rcases adj_cases h3 with a3 | a3 | a3
    all_goals first
      | exact h12 (a1.trans a2.symm)
      | exact h13 (a1.trans a3.symm)
      | exact h23 (a2.trans a3.symm)
      | exact h12 (same _ _ ⟨a1.1, a2.1, by omega⟩)
      | exact h13 (same _ _ ⟨a1.1, a3.1, by omega⟩)
      | exact h23 (same _ _ ⟨a2.1, a3.1, by omega⟩)
      | exact help _ _ _ a1 a2 a3 f1 f2 f3
      | exact help _ _ _ a1 a3 a2 f1 f3 f2
      | exact help _ _ _ a2 a1 a3 f2 f1 f3
      | exact help _ _ _ a2 a3 a1 f2 f3 f1
      | exact help _ _ _ a3 a1 a2 f3 f1 f2
      | exact help _ _ _ a3 a2 a1 f3 f2 f1

theorem valid_iff_model (f : Cell n → Fin 4) : Valid f ↔ Model f :=
  ⟨model_of_valid, valid_of_model⟩

/-- A164754 counts the arrays of the interval characterisation. -/
theorem a_eq_model (n : ℕ) :
    a n = open Classical in (Finset.univ.filter (fun f : Cell n → Fin 4 => Model f)).card := by
  classical
  unfold a
  congr 1
  exact Finset.filter_congr (fun f _ => valid_iff_model f)

open Finset

theorem pairs_card (N : ℕ) : ∀ m, m < N →
    ((range N ×ˢ range N).filter (fun p : ℕ × ℕ => 1 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ m)).card * 2
      = m * (m - 1) := by
  intro m
  induction m with
  | zero =>
    intro _
    have : (range N ×ˢ range N).filter (fun p : ℕ × ℕ => 1 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ 0) = ∅ := by
      ext p; simp; omega
    rw [this]; rfl
  | succ m ih =>
    intro hm
    have hsplit : (range N ×ˢ range N).filter (fun p : ℕ × ℕ => 1 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ m + 1) =
        (range N ×ˢ range N).filter (fun p : ℕ × ℕ => 1 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ m) ∪
        (Icc 1 m).image (fun x => (x, m + 1)) := by
      ext ⟨x, y⟩
      simp only [mem_filter, mem_product, mem_range, mem_union, mem_image, mem_Icc, Prod.mk.injEq]
      constructor
      · intro h
        by_cases hy : y ≤ m
        · left; omega
        · right; exact ⟨x, by omega, rfl, by omega⟩
      · rintro (h | ⟨z, hz, rfl, rfl⟩) <;> omega
    have hdisj : Disjoint ((range N ×ˢ range N).filter (fun p : ℕ × ℕ => 1 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ m))
        ((Icc 1 m).image (fun x => (x, m + 1))) := by
      rw [Finset.disjoint_left]
      rintro ⟨x, y⟩ h1 h2
      simp only [mem_filter, mem_image, Prod.mk.injEq] at h1 h2
      obtain ⟨z, _, _, h3⟩ := h2
      omega
    have hinj : Function.Injective (fun x : ℕ => (x, m + 1)) := fun a b h => by simpa using h
    rw [hsplit, card_union_of_disjoint hdisj, card_image_of_injective _ hinj, Nat.card_Icc]
    have := ih (by omega)
    rcases m with _ | k
    · simp
      intros
      omega
    · simp only [Nat.add_sub_cancel] at this ⊢
      nlinarith [this]

theorem square_card (n : ℕ) :
    ((range n ×ˢ range n).filter (fun p : ℕ × ℕ => 1 ≤ p.1 ∧ 1 ≤ p.2)).card = (n - 1) * (n - 1) := by
  have : (range n ×ˢ range n).filter (fun p : ℕ × ℕ => 1 ≤ p.1 ∧ 1 ≤ p.2) = Icc 1 (n - 1) ×ˢ Icc 1 (n - 1) := by
    ext ⟨x, y⟩; simp; omega
  rw [this, card_product, Nat.card_Icc, Nat.add_sub_cancel]

theorem line_card (n : ℕ) :
    ((range n ×ˢ range n).filter (fun p : ℕ × ℕ => 1 ≤ p.1 ∧ p.1 + 3 ≤ n ∧ p.2 = 0)).card = n - 3 := by
  have : (range n ×ˢ range n).filter (fun p : ℕ × ℕ => 1 ≤ p.1 ∧ p.1 + 3 ≤ n ∧ p.2 = 0)
      = Icc 1 (n - 3) ×ˢ {0} := by
    ext ⟨x, y⟩; simp; omega
  rw [this, card_product, Nat.card_Icc]
  simp

/-- Threshold tuples `(u1, u2, u3, v1, v2, v3)`. -/
abbrev Tup := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ

/-- Constraints on the thresholds of a counted array. -/
def Cn (n : ℕ) (τ : Tup) : Prop :=
  let u1 := τ.1; let u2 := τ.2.1; let u3 := τ.2.2.1
  let v1 := τ.2.2.2.1; let v2 := τ.2.2.2.2.1; let v3 := τ.2.2.2.2.2
  1 ≤ u1 ∧ u1 ≤ u2 ∧ u2 ≤ u3 ∧ u3 + 1 ≤ n ∧ 1 ≤ v1 ∧ v1 ≤ v2 ∧ v2 ≤ v3 ∧ v3 + 1 ≤ n ∧
  (u1 < u2 → v1 = u1 + 1) ∧ (u2 < u3 → v3 + 1 = u3) ∧
  (v1 < v2 → u1 = v1 + 1) ∧ (v2 < v3 → u3 + 1 = v3)

instance (n : ℕ) (τ : Tup) : Decidable (Cn n τ) := by unfold Cn; infer_instance

def T (n : ℕ) : Finset Tup :=
  (range n ×ˢ range n ×ˢ range n ×ˢ range n ×ˢ range n ×ˢ range n).filter (Cn n)

/-- Parameter domains of the nine families. -/
def dom (n t x y : ℕ) : Prop :=
  if t = 0 then 1 ≤ x ∧ 1 ≤ y
  else if t ≤ 4 then 1 ≤ x ∧ x < y
  else if t ≤ 6 then 1 ≤ x ∧ x < y ∧ y + 2 ≤ n
  else if t ≤ 8 then 1 ≤ x ∧ x + 3 ≤ n ∧ y = 0
  else False

instance (n t x y : ℕ) : Decidable (dom n t x y) := by unfold dom; infer_instance

def D (n : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (range 9 ×ˢ range n ×ˢ range n).filter (fun p => dom n p.1 p.2.1 p.2.2)

/-- The nine families. -/
def Φ (p : ℕ × ℕ × ℕ) : Tup :=
  let t := p.1; let x := p.2.1; let y := p.2.2
  if t = 0 then (x, x, x, y, y, y)
  else if t = 1 then (x, y, y, x + 1, x + 1, x + 1)
  else if t = 2 then (x, x, y, y - 1, y - 1, y - 1)
  else if t = 3 then (x + 1, x + 1, x + 1, x, y, y)
  else if t = 4 then (y - 1, y - 1, y - 1, x, x, y)
  else if t = 5 then (x, y, y, x + 1, x + 1, y + 1)
  else if t = 6 then (x + 1, x + 1, y + 1, x, y, y)
  else if t = 7 then (x, x + 1, x + 2, x + 1, x + 1, x + 1)
  else (x + 1, x + 1, x + 1, x, x + 1, x + 2)

def ψ (τ : Tup) : ℕ × ℕ × ℕ :=
  let u1 := τ.1; let u2 := τ.2.1; let u3 := τ.2.2.1
  let v1 := τ.2.2.2.1; let v2 := τ.2.2.2.2.1; let v3 := τ.2.2.2.2.2
  if u1 < u2 ∧ u2 < u3 then (7, u1, 0)
  else if v1 < v2 ∧ v2 < v3 then (8, v1, 0)
  else if u1 < u2 ∧ v2 < v3 then (5, u1, u2)
  else if u2 < u3 ∧ v1 < v2 then (6, v1, v2)
  else if u1 < u2 then (1, u1, u2)
  else if u2 < u3 then (2, u1, u3)
  else if v1 < v2 then (3, v1, v2)
  else if v2 < v3 then (4, v1, v3)
  else (0, u1, v1)

theorem card_T_eq_D (n : ℕ) : (T n).card = (D n).card := by
  symm
  apply Finset.card_nbij' Φ ψ
  · rintro ⟨t, x, y⟩ h
    simp only [D, Finset.mem_coe, mem_filter, mem_product, mem_range] at h
    obtain ⟨⟨ht, hx, hy⟩, hd⟩ := h
    simp only [T, Finset.mem_coe, mem_filter, mem_product, mem_range, Cn, Φ]
    unfold dom at hd
    interval_cases t <;> simp at hd ⊢ <;> omega
  · rintro ⟨u1, u2, u3, v1, v2, v3⟩ h
    simp only [T, Finset.mem_coe, mem_filter, mem_product, mem_range, Cn] at h
    simp only [D, Finset.mem_coe, mem_filter, mem_product, mem_range, ψ]
    split_ifs <;> simp [dom] <;> omega
  · rintro ⟨t, x, y⟩ h
    simp only [D, Finset.mem_coe, mem_filter, mem_product, mem_range] at h
    obtain ⟨⟨ht, hx, hy⟩, hd⟩ := h
    unfold dom at hd
    interval_cases t <;> simp at hd <;> simp [Φ, ψ] <;> omega
  · rintro ⟨u1, u2, u3, v1, v2, v3⟩ h
    simp only [T, Finset.mem_coe, mem_filter, mem_product, mem_range, Cn] at h
    simp only [ψ]
    split_ifs <;> simp [Φ] <;> omega

theorem card_D (n : ℕ) : (D n).card =
    (n - 1) * (n - 1) +
    4 * ((range n ×ˢ range n).filter (fun p : ℕ × ℕ => 1 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ n - 1)).card +
    2 * ((range n ×ˢ range n).filter (fun p : ℕ × ℕ => 1 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ n - 2)).card +
    2 * (n - 3) := by
  have key : ∀ t, (D n).filter (fun p => p.1 = t) =
      ((range n ×ˢ range n).filter (fun q : ℕ × ℕ => t < 9 ∧ dom n t q.1 q.2)).map
        ⟨fun q => (t, q), fun a b h => by simpa using h⟩ := by
    intro t
    ext ⟨t', x, y⟩
    simp only [D, mem_filter, mem_product, mem_range, mem_map, Prod.exists]
    constructor
    · rintro ⟨⟨⟨h1, h2, h3⟩, h4⟩, rfl⟩
      exact ⟨x, y, ⟨⟨h2, h3⟩, h1, h4⟩, rfl⟩
    · rintro ⟨a, b, ⟨⟨h2, h3⟩, h1, h4⟩, h5⟩
      cases h5
      exact ⟨⟨⟨h1, h2, h3⟩, h4⟩, rfl⟩
  have split : (D n).card = ∑ t ∈ range 9, ((D n).filter (fun p => p.1 = t)).card := by
    rw [← Finset.card_biUnion]
    · congr 1
      ext ⟨t, x, y⟩
      simp only [mem_biUnion, mem_filter, mem_range]
      constructor
      · intro h
        refine ⟨t, ?_, h, rfl⟩
        simp only [D, mem_filter, mem_product, mem_range] at h
        exact h.1.1
      · rintro ⟨_, _, h, _⟩; exact h
    · intro a _ b _ hab
      simp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro p h1 h2
      simp only [mem_filter] at h1 h2
      exact hab (h1.2.symm.trans h2.2)
  rw [split]
  simp only [key, card_map, Finset.sum_range_succ, Finset.sum_range_zero]
  have e0 : ((range n ×ˢ range n).filter (fun q : ℕ × ℕ => 0 < 9 ∧ dom n 0 q.1 q.2)) =
      (range n ×ˢ range n).filter (fun p : ℕ × ℕ => 1 ≤ p.1 ∧ 1 ≤ p.2) := by
    apply filter_congr; intro q _; simp [dom]
  have e1 : ∀ t, 1 ≤ t → t ≤ 4 →
      ((range n ×ˢ range n).filter (fun q : ℕ × ℕ => t < 9 ∧ dom n t q.1 q.2)) =
      (range n ×ˢ range n).filter (fun p : ℕ × ℕ => 1 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ n - 1) := by
    intro t h1 h2
    apply filter_congr; intro q hq
    simp only [mem_product, mem_range] at hq
    unfold dom
    split_ifs <;> omega
  have e5 : ∀ t, 5 ≤ t → t ≤ 6 →
      ((range n ×ˢ range n).filter (fun q : ℕ × ℕ => t < 9 ∧ dom n t q.1 q.2)) =
      (range n ×ˢ range n).filter (fun p : ℕ × ℕ => 1 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ n - 2) := by
    intro t h1 h2
    apply filter_congr; intro q hq
    simp only [mem_product, mem_range] at hq
    unfold dom
    split_ifs <;> omega
  have e7 : ∀ t, 7 ≤ t → t ≤ 8 →
      ((range n ×ˢ range n).filter (fun q : ℕ × ℕ => t < 9 ∧ dom n t q.1 q.2)) =
      (range n ×ˢ range n).filter (fun p : ℕ × ℕ => 1 ≤ p.1 ∧ p.1 + 3 ≤ n ∧ p.2 = 0) := by
    intro t h1 h2
    apply filter_congr; intro q hq
    simp only [mem_product, mem_range] at hq
    unfold dom
    split_ifs <;> omega
  rw [e0, e1 1 le_rfl (by norm_num), e1 2 (by norm_num) (by norm_num), e1 3 (by norm_num) (by norm_num),
    e1 4 (by norm_num) le_rfl, e5 5 le_rfl (by norm_num), e5 6 (by norm_num) le_rfl,
    e7 7 le_rfl (by norm_num), e7 8 (by norm_num) le_rfl, square_card, line_card]
  ring

theorem card_T (n : ℕ) (hn : 3 ≤ n) : ((T n).card : ℤ) = 4 * (n : ℤ) ^ 2 - 11 * n + 5 := by
  rw [card_T_eq_D, card_D]
  have h1 := pairs_card n (n - 1) (by omega)
  have h2 := pairs_card n (n - 2) (by omega)
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
  simp only [show k + 3 - 1 = k + 2 by omega, show k + 3 - 2 = k + 1 by omega,
    show k + 3 - 3 = k by omega, show k + 2 - 1 = k + 1 by omega, show k + 1 - 1 = k by omega] at h1 h2 ⊢
  push_cast
  have h1' : ((((range (k + 3) ×ˢ range (k + 3)).filter
      (fun p : ℕ × ℕ => 1 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ k + 2)).card : ℕ) : ℤ) * 2 = (k + 2) * (k + 1) := by
    exact_mod_cast h1
  have h2' : ((((range (k + 3) ×ˢ range (k + 3)).filter
      (fun p : ℕ × ℕ => 1 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ k + 1)).card : ℕ) : ℤ) * 2 = (k + 1) * k := by
    exact_mod_cast h2
  linarith

/-! ## From arrays to thresholds -/

/-- Column `j` of `f` as a function of the row; rows `≥ n` read as the bottom value. -/
def col (f : Cell n → Fin 4) (j : Bool) (r : ℕ) : Fin 4 :=
  if h : r < n then f (⟨r, h⟩, j) else (if j then 3 else 2)

/-- Position of a value in the block order of a column: left 1, 2, 4, 3; right 2, 1, 3, 4. -/
def rk (j : Bool) (c : Fin 4) : ℕ := if j then ![1, 0, 2, 3] c else ![0, 1, 3, 2] c

theorem rk_le (j : Bool) (c : Fin 4) : rk j c ≤ 3 := by
  cases j <;> fin_cases c <;> decide

theorem col_lt {f : Cell n → Fin 4} {j : Bool} {r : ℕ} (h : r < n) : col f j r = f (⟨r, h⟩, j) := by
  simp [col, h]

theorem col_ge {f : Cell n → Fin 4} {j : Bool} {r : ℕ} (h : n ≤ r) :
    col f j r = (if j then 3 else 2) := by
  simp [col, show ¬ r < n by omega]

theorem top' {f : Cell n → Fin 4} (hm : Model f) (j : Bool) (hn : 0 < n) :
    col f j 0 = (if j then 1 else 0) := by
  rw [col_lt hn]; exact hm.top _ rfl

theorem bot' {f : Cell n → Fin 4} (hm : Model f) (j : Bool) (hn : 0 < n) :
    col f j (n - 1) = (if j then 3 else 2) := by
  rw [col_lt (by omega)]; exact hm.bot _ (by simp; omega)

theorem interval' {f : Cell n → Fin 4} (hm : Model f) (j : Bool) {a r b : ℕ} (har : a < r)
    (hrb : r < b) (hb : b < n) (h : col f j a = col f j b) : col f j r = col f j a := by
  rw [col_lt (by omega), col_lt (by omega)] at h ⊢
  exact hm.interval j ⟨a, by omega⟩ ⟨b, hb⟩ ⟨r, by omega⟩ h har hrb

theorem meet' {f : Cell n → Fin 4} (hm : Model f) {i k : ℕ} (hi : i < n) (hk : k < n)
    (h : col f false i = col f true k) :
    ∃ s, s < n ∧ col f false s = col f false i ∧ col f true s = col f false i := by
  rw [col_lt hi, col_lt hk] at h
  obtain ⟨s, h1, h2⟩ := hm.meet ⟨i, hi⟩ ⟨k, hk⟩ h
  exact ⟨s.val, s.isLt, by rw [col_lt s.isLt, col_lt hi]; exact h1,
    by rw [col_lt s.isLt, col_lt hi]; exact h2⟩

theorem ends' {f : Cell n → Fin 4} (hm : Model f) (j : Bool) {s : ℕ} (h1 : 1 ≤ s) (h2 : s + 1 < n)
    (hs : col f false s = col f true s) (hu : col f j (s - 1) = col f j s)
    (hv : col f j (s + 1) = col f j s) : False := by
  rw [col_lt (by omega), col_lt (by omega)] at hs
  rw [col_lt (by omega), col_lt (by omega)] at hu hv
  exact hm.ends ⟨s, by omega⟩ ⟨s - 1, by omega⟩ ⟨s + 1, h2⟩ j hs (by simp; omega) rfl hu hv

/-- Left column: ranks increase downwards. -/
theorem monoL {f : Cell n → Fin 4} (hm : Model f) {r r' : ℕ} (hrr : r ≤ r') :
    rk false (col f false r) ≤ rk false (col f false r') := by
  by_cases hr'' : n ≤ r'
  · rw [col_ge hr'']; exact rk_le _ _
  have hr' : r' < n := by omega
  rcases Nat.eq_or_lt_of_le hrr with h | hlt
  · rw [h]
  have hn : 0 < n := by omega
  have t0 := top' hm false hn
  have t1 := top' hm true hn
  have b0 := bot' hm false hn
  have b1 := bot' hm true hn
  simp only [Bool.false_eq_true, ↓reduceIte] at t0 t1 b0 b1
  -- the bad pairs
  have caseTop : col f false r' = 0 → col f false r ≠ 0 → False := by
    intro hb ha
    rcases Nat.eq_zero_or_pos r with h0 | h0
    · subst h0; exact ha t0
    · have := interval' hm false h0 hlt hr' (t0.trans hb.symm)
      exact ha (this.trans t0)
  have caseBot : col f false r = 2 → col f false r' ≠ 2 → False := by
    intro ha hb
    rcases Nat.eq_or_lt_of_le (show r' ≤ n - 1 by omega) with h1 | h1
    · rw [h1] at hb; exact hb b0
    · have := interval' hm false hlt h1 (by omega) (ha.trans b0.symm)
      exact hb (this.trans ha)
  have caseCross : col f false r = 3 → col f false r' = 1 → False := by
    intro ha hb
    obtain ⟨s1, hs1n, hs1L, hs1R⟩ := meet' hm hr' hn (hb.trans t1.symm)
    obtain ⟨s3, hs3n, hs3L, hs3R⟩ := meet' hm (show r < n by omega) (show n - 1 < n by omega)
      (ha.trans b1.symm)
    rw [hb] at hs1L hs1R
    rw [ha] at hs3L hs3R
    -- s1 lies below r
    have h1 : r < s1 := by
      by_contra hc
      rcases Nat.eq_or_lt_of_le (not_lt.mp hc) with h | h
      · rw [← h, hs1L] at ha; exact absurd ha (by decide)
      · have := interval' hm false h hlt hr' (hs1L.trans hb.symm)
        rw [this, hs1L] at ha; exact absurd ha (by decide)
    -- s3 lies above r'
    have h3 : s3 < r' := by
      by_contra hc
      rcases Nat.eq_or_lt_of_le (not_lt.mp hc) with h | h
      · rw [h, hs3L] at hb; exact absurd hb (by decide)
      · have := interval' hm false hlt h hs3n (ha.trans hs3L.symm)
        rw [this, ha] at hb; exact absurd hb (by decide)
    -- in the right column, s1 lies above s3
    have h13 : s1 < s3 := by
      by_contra hc
      rcases Nat.eq_or_lt_of_le (not_lt.mp hc) with h | h
      · rw [h, hs1R] at hs3R; exact absurd hs3R (by decide)
      · rcases Nat.eq_zero_or_pos s3 with h0 | h0
        · rw [h0, t1] at hs3R; exact absurd hs3R (by decide)
        · have := interval' hm true h0 h hs1n (t1.trans hs1R.symm)
          rw [this, t1] at hs3R; exact absurd hs3R (by decide)
    have := interval' hm false h1 h13 hs3n (ha.trans hs3L.symm)
    rw [this, ha] at hs1L; exact absurd hs1L (by decide)
  by_contra hc'
  have hc := not_le.mp hc'
  generalize ha : col f false r = a at caseTop caseBot caseCross hc
  generalize hb : col f false r' = b at caseTop caseBot caseCross hc
  fin_cases a <;> fin_cases b <;> simp [rk] at hc <;>
    first
    | exact caseTop rfl (by decide)
    | exact caseBot rfl (by decide)
    | exact caseCross rfl rfl

/-- Swap of the values 1 <-> 2 and 3 <-> 4 (colours 0 <-> 1, 2 <-> 3). -/
def sw (c : Fin 4) : Fin 4 := ![1, 0, 3, 2] c

theorem sw_sw (c : Fin 4) : sw (sw c) = c := by fin_cases c <;> rfl

theorem sw_inj {a b : Fin 4} (h : sw a = sw b) : a = b := by rw [← sw_sw a, h, sw_sw]

/-- Left-right mirror image, with the values swapped so that the corners stay in place. -/
def mir (f : Cell n → Fin 4) : Cell n → Fin 4 := fun x => sw (f (x.1, !x.2))

theorem col_mir (f : Cell n → Fin 4) (j : Bool) (r : ℕ) : col (mir f) j r = sw (col f (!j) r) := by
  by_cases h : r < n
  · rw [col_lt h, col_lt h]; rfl
  · rw [col_ge (by omega), col_ge (by omega)]; cases j <;> rfl

theorem rk_sw (j : Bool) (c : Fin 4) : rk j (sw c) = rk (!j) c := by
  cases j <;> fin_cases c <;> rfl

theorem model_mir {f : Cell n → Fin 4} (hm : Model f) : Model (mir f) where
  top := by
    rintro ⟨i, j⟩ hx
    simp only [mir]
    rw [hm.top (i, !j) hx]
    cases j <;> rfl
  bot := by
    rintro ⟨i, j⟩ hx
    simp only [mir]
    rw [hm.bot (i, !j) hx]
    cases j <;> rfl
  interval := by
    intro j i k r h h1 h2
    simp only [mir] at h ⊢
    rw [hm.interval (!j) i k r (sw_inj h) h1 h2]
  meet := by
    intro i k h
    simp only [mir, Bool.not_false, Bool.not_true] at h ⊢
    have h' := sw_inj h
    obtain ⟨s, h1, h2⟩ := hm.meet k i h'.symm
    exact ⟨s, congrArg sw (h2.trans h'.symm), congrArg sw (h1.trans h'.symm)⟩
  ends := by
    intro s u v j hs hu hv hfu hfv
    simp only [mir, Bool.not_false, Bool.not_true] at hs hfu hfv
    exact hm.ends s u v (!j) (sw_inj hs).symm hu hv (sw_inj hfu) (sw_inj hfv)

/-- Both columns: ranks increase downwards. -/
theorem mono {f : Cell n → Fin 4} (hm : Model f) (j : Bool) {r r' : ℕ} (h : r ≤ r') :
    rk j (col f j r) ≤ rk j (col f j r') := by
  cases j
  · exact monoL hm h
  · have := monoL (model_mir hm) h
    rwa [col_mir, col_mir, rk_sw, rk_sw] at this

theorem exists_thr (f : Cell n → Fin 4) (j : Bool) (k : ℕ) : ∃ r, min k 3 ≤ rk j (col f j r) :=
  ⟨n, by rw [col_ge le_rfl]; cases j <;> simp [rk]⟩

/-- First row of column `j` whose rank is at least `k`. -/
def thr (f : Cell n → Fin 4) (j : Bool) (k : ℕ) : ℕ := Nat.find (exists_thr f j k)

theorem thr_spec {f : Cell n → Fin 4} (hm : Model f) (j : Bool) {k : ℕ} (hk : k ≤ 3) (r : ℕ) :
    k ≤ rk j (col f j r) ↔ thr f j k ≤ r := by
  have hmin : min k 3 = k := min_eq_left hk
  constructor
  · intro h
    exact Nat.find_min' (exists_thr f j k) (by rw [hmin]; exact h)
  · intro h
    have := Nat.find_spec (exists_thr f j k)
    exact le_trans (le_trans hmin.symm.le this) (mono hm j h)

/-- Left column with thresholds `a ≤ b ≤ c`: blocks of 1, 2, 4, 3 (colours 0, 1, 3, 2). -/
def bL (a b c r : ℕ) : Fin 4 := if r < a then 0 else if r < b then 1 else if r < c then 3 else 2
/-- Right column with thresholds `a ≤ b ≤ c`: blocks of 2, 1, 3, 4 (colours 1, 0, 2, 3). -/
def bR (a b c r : ℕ) : Fin 4 := if r < a then 1 else if r < b then 0 else if r < c then 2 else 3

theorem col_eq_bL {f : Cell n → Fin 4} (hm : Model f) (r : ℕ) :
    col f false r = bL (thr f false 1) (thr f false 2) (thr f false 3) r := by
  have s1 := thr_spec hm false (k := 1) (by norm_num) r
  have s2 := thr_spec hm false (k := 2) (by norm_num) r
  have s3 := thr_spec hm false (k := 3) (by norm_num) r
  generalize col f false r = c at s1 s2 s3
  unfold bL
  fin_cases c <;> simp [rk] at s1 s2 s3 <;> split_ifs <;> first | rfl | (exfalso; omega)

theorem col_eq_bR {f : Cell n → Fin 4} (hm : Model f) (r : ℕ) :
    col f true r = bR (thr f true 1) (thr f true 2) (thr f true 3) r := by
  have s1 := thr_spec hm true (k := 1) (by norm_num) r
  have s2 := thr_spec hm true (k := 2) (by norm_num) r
  have s3 := thr_spec hm true (k := 3) (by norm_num) r
  generalize col f true r = c at s1 s2 s3
  unfold bR
  fin_cases c <;> simp [rk] at s1 s2 s3 <;> split_ifs <;> first | rfl | (exfalso; omega)

theorem thr_mir {f : Cell n → Fin 4} (hm : Model f) (j : Bool) {k : ℕ} (hk : k ≤ 3) :
    thr (mir f) j k = thr f (!j) k := by
  have hm' := model_mir hm
  have key : ∀ r, thr (mir f) j k ≤ r ↔ thr f (!j) k ≤ r := by
    intro r
    rw [← thr_spec hm' j hk, ← thr_spec hm (!j) hk, col_mir, rk_sw]
  exact le_antisymm ((key _).mpr le_rfl) ((key _).mp le_rfl)

theorem thr_basic {f : Cell n → Fin 4} (hm : Model f) (hn : 0 < n) (j : Bool) :
    1 ≤ thr f j 1 ∧ thr f j 1 ≤ thr f j 2 ∧ thr f j 2 ≤ thr f j 3 ∧ thr f j 3 + 1 ≤ n := by
  have s1 := thr_spec hm j (k := 1) (by norm_num)
  have s2 := thr_spec hm j (k := 2) (by norm_num)
  have s3 := thr_spec hm j (k := 3) (by norm_num)
  refine ⟨?_, ?_, ?_, ?_⟩
  · by_contra hc
    have := (s1 0).mpr (by omega)
    rw [top' hm j hn] at this
    cases j <;> simp [rk] at this
  · exact (s1 _).mp (le_trans (by norm_num) ((s2 _).mpr le_rfl))
  · exact (s2 _).mp (le_trans (by norm_num) ((s3 _).mpr le_rfl))
  · have := (s3 (n - 1)).mp (by rw [bot' hm j hn]; cases j <;> simp [rk])
    omega

theorem bL_one {a b c r : ℕ} : bL a b c r = 1 ↔ a ≤ r ∧ r < b := by
  unfold bL; split_ifs <;> simp <;> omega
theorem bL_three {a b c r : ℕ} : bL a b c r = 3 ↔ a ≤ r ∧ b ≤ r ∧ r < c := by
  unfold bL; split_ifs <;> simp <;> omega
theorem bR_one {a b c r : ℕ} : bR a b c r = 1 ↔ r < a := by
  unfold bR; split_ifs <;> simp <;> omega
theorem bR_three {a b c r : ℕ} : bR a b c r = 3 ↔ a ≤ r ∧ b ≤ r ∧ c ≤ r := by
  unfold bR; split_ifs <;> simp <;> omega

/-- If value 2 appears in the left column, the shared row is the first one of its block and the
right column's block of 2s ends there. -/
theorem cross1 {f : Cell n → Fin 4} (hm : Model f) (hn : 0 < n) :
    thr f false 1 < thr f false 2 → thr f true 1 = thr f false 1 + 1 := by
  intro h12
  have hL := col_eq_bL hm
  have hR := col_eq_bR hm
  obtain ⟨a1, a2, a3, a4⟩ := thr_basic hm hn false
  obtain ⟨c1, c2, c3, c4⟩ := thr_basic hm hn true
  obtain ⟨s, hsn, hsL, hsR⟩ := meet' hm (i := thr f false 1) (k := 0) (by omega) hn
    (by simp only [hL, hR, bL, bR]; split_ifs <;> first | rfl | (exfalso; omega))
  have e : col f false (thr f false 1) = 1 := by
    simp only [hL, bL]; split_ifs <;> first | rfl | (exfalso; omega)
  rw [e, hL, bL_one] at hsL
  rw [e, hR, bR_one] at hsR
  have hsv : s + 1 = thr f true 1 := by
    by_contra hc
    exact ends' hm true (s := s) (by omega) (by omega)
      (by simp only [hL, hR, bL, bR]; split_ifs <;> first | rfl | (exfalso; omega))
      (by simp only [hR, bR]; split_ifs <;> first | rfl | (exfalso; omega))
      (by simp only [hR, bR]; split_ifs <;> first | rfl | (exfalso; omega))
  have hsu : s = thr f false 1 := by
    by_contra hc
    exact ends' hm true (s := s - 1) (by omega) (by omega)
      (by simp only [hL, hR, bL, bR]; split_ifs <;> first | rfl | (exfalso; omega))
      (by simp only [hR, bR]; split_ifs <;> first | rfl | (exfalso; omega))
      (by simp only [hR, bR]; split_ifs <;> first | rfl | (exfalso; omega))
  omega

/-- If value 4 appears in the left column, the shared row is the last one of its block and the
right column's block of 4s starts there. -/
theorem cross2 {f : Cell n → Fin 4} (hm : Model f) (hn : 0 < n) :
    thr f false 2 < thr f false 3 → thr f true 3 + 1 = thr f false 3 := by
  intro h23
  have hL := col_eq_bL hm
  have hR := col_eq_bR hm
  obtain ⟨a1, a2, a3, a4⟩ := thr_basic hm hn false
  obtain ⟨c1, c2, c3, c4⟩ := thr_basic hm hn true
  obtain ⟨s, hsn, hsL, hsR⟩ := meet' hm (i := thr f false 3 - 1) (k := n - 1) (by omega) (by omega)
    (by simp only [hL, hR, bL, bR]; split_ifs <;> first | rfl | (exfalso; omega))
  have e : col f false (thr f false 3 - 1) = 3 := by
    simp only [hL, bL]; split_ifs <;> first | rfl | (exfalso; omega)
  rw [e, hL, bL_three] at hsL
  rw [e, hR, bR_three] at hsR
  have hs1 : s = thr f true 3 := by
    by_contra hc
    exact ends' hm true (s := s) (by omega) (by omega)
      (by simp only [hL, hR, bL, bR]; split_ifs <;> first | rfl | (exfalso; omega))
      (by simp only [hR, bR]; split_ifs <;> first | rfl | (exfalso; omega))
      (by simp only [hR, bR]; split_ifs <;> first | rfl | (exfalso; omega))
  have hs2 : s + 1 = thr f false 3 := by
    by_contra hc
    exact ends' hm true (s := s + 1) (by omega) (by omega)
      (by simp only [hL, hR, bL, bR]; split_ifs <;> first | rfl | (exfalso; omega))
      (by simp only [hR, bR]; split_ifs <;> first | rfl | (exfalso; omega))
      (by simp only [hR, bR]; split_ifs <;> first | rfl | (exfalso; omega))
  omega

theorem cross3 {f : Cell n → Fin 4} (hm : Model f) (hn : 0 < n) :
    thr f true 1 < thr f true 2 → thr f false 1 = thr f true 1 + 1 := by
  have := cross1 (model_mir hm) hn
  simp only [thr_mir hm _ (show 1 ≤ 3 by norm_num), thr_mir hm _ (show 2 ≤ 3 by norm_num),
    Bool.not_false, Bool.not_true] at this
  exact this

theorem cross4 {f : Cell n → Fin 4} (hm : Model f) (hn : 0 < n) :
    thr f true 2 < thr f true 3 → thr f false 3 + 1 = thr f true 3 := by
  have := cross2 (model_mir hm) hn
  simp only [thr_mir hm _ (show 2 ≤ 3 by norm_num), thr_mir hm _ (show 3 ≤ 3 by norm_num),
    Bool.not_false, Bool.not_true] at this
  exact this

/-- The thresholds of an array. -/
def tau (f : Cell n → Fin 4) : Tup :=
  (thr f false 1, thr f false 2, thr f false 3, thr f true 1, thr f true 2, thr f true 3)

/-- The array with given thresholds. -/
def build (τ : Tup) : Cell n → Fin 4 := fun x =>
  if x.2 then bR τ.2.2.2.1 τ.2.2.2.2.1 τ.2.2.2.2.2 x.1 else bL τ.1 τ.2.1 τ.2.2.1 x.1

theorem tau_mem {f : Cell n → Fin 4} (hm : Model f) (hn : 0 < n) : tau f ∈ T n := by
  obtain ⟨a1, a2, a3, a4⟩ := thr_basic hm hn false
  obtain ⟨c1, c2, c3, c4⟩ := thr_basic hm hn true
  have x1 := cross1 hm hn
  have x2 := cross2 hm hn
  have x3 := cross3 hm hn
  have x4 := cross4 hm hn
  simp only [T, mem_filter, mem_product, mem_range, Cn, tau]
  omega

theorem build_tau {f : Cell n → Fin 4} (hm : Model f) : build (tau f) = f := by
  funext ⟨i, j⟩
  cases j
  · simp only [build, tau, Bool.false_eq_true, ↓reduceIte]
    rw [← col_eq_bL hm, col_lt i.isLt]
  · simp only [build, tau, ↓reduceIte]
    rw [← col_eq_bR hm, col_lt i.isLt]

theorem model_build {τ : Tup} (hτ : Cn n τ) : Model (build (n := n) τ) := by
  obtain ⟨u1, u2, u3, v1, v2, v3⟩ := τ
  simp only [Cn] at hτ
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := hτ
  constructor
  · rintro ⟨i, j⟩ hx
    simp only at hx
    cases j <;> simp only [build, bL, bR, Bool.false_eq_true, ↓reduceIte] <;>
      split_ifs <;> first | rfl | (exfalso; omega)
  · rintro ⟨i, j⟩ hx
    simp only at hx
    cases j <;> simp only [build, bL, bR, Bool.false_eq_true, ↓reduceIte] <;>
      split_ifs <;> first | rfl | (exfalso; omega)
  · intro j i k r h hir hrk
    cases j <;> simp only [build, bL, bR, Bool.false_eq_true, ↓reduceIte] at h ⊢ <;>
      split_ifs at h ⊢ <;> first | rfl | (exfalso; omega)
  · intro i k h
    simp only [build, Bool.false_eq_true, ↓reduceIte] at h ⊢
    unfold bL bR at h
    split_ifs at h <;>
      first
      | exact absurd h (by decide)
      | (refine ⟨⟨v1, by omega⟩, ?_, ?_⟩ <;> simp only [bL, bR] <;> split_ifs <;>
          first | rfl | (exfalso; omega))
      | (refine ⟨⟨u1, by omega⟩, ?_, ?_⟩ <;> simp only [bL, bR] <;> split_ifs <;>
          first | rfl | (exfalso; omega))
      | (refine ⟨⟨v3, by omega⟩, ?_, ?_⟩ <;> simp only [bL, bR] <;> split_ifs <;>
          first | rfl | (exfalso; omega))
      | (refine ⟨⟨u3, by omega⟩, ?_, ?_⟩ <;> simp only [bL, bR] <;> split_ifs <;>
          first | rfl | (exfalso; omega))
  · intro s u v j hs hu hv hfu hfv
    simp only [build, Bool.false_eq_true, ↓reduceIte] at hs hfu hfv
    unfold bL bR at hs
    split_ifs at hs <;> (try exact absurd hs (by decide)) <;>
      (cases j <;> simp only [bL, bR, Bool.false_eq_true, ↓reduceIte] at hfu hfv <;>
        split_ifs at hfu hfv <;>
        first
        | exact absurd hfu (by decide)
        | exact absurd hfv (by decide)
        | omega)

theorem col_build_L {τ : Tup} (hτ : τ ∈ T n) (r : ℕ) :
    col (build (n := n) τ) false r = bL τ.1 τ.2.1 τ.2.2.1 r := by
  obtain ⟨u1, u2, u3, v1, v2, v3⟩ := τ
  simp only [T, mem_filter, mem_product, mem_range, Cn] at hτ
  by_cases h : r < n
  · rw [col_lt h]; rfl
  · rw [col_ge (by omega)]; simp only [bL, Bool.false_eq_true, ↓reduceIte]
    split_ifs <;> first | rfl | (exfalso; omega)

theorem col_build_R {τ : Tup} (hτ : τ ∈ T n) (r : ℕ) :
    col (build (n := n) τ) true r = bR τ.2.2.2.1 τ.2.2.2.2.1 τ.2.2.2.2.2 r := by
  obtain ⟨u1, u2, u3, v1, v2, v3⟩ := τ
  simp only [T, mem_filter, mem_product, mem_range, Cn] at hτ
  by_cases h : r < n
  · rw [col_lt h]; rfl
  · rw [col_ge (by omega)]; simp only [bR, ↓reduceIte]
    split_ifs <;> first | rfl | (exfalso; omega)

theorem thr_eq_of {f : Cell n → Fin 4} {j : Bool} {k a : ℕ} (h : ∀ r, thr f j k ≤ r ↔ a ≤ r) :
    thr f j k = a :=
  le_antisymm ((h a).mpr le_rfl) ((h _).mp le_rfl)

theorem tau_build {τ : Tup} (hτ : τ ∈ T n) : tau (build (n := n) τ) = τ := by
  have hm := model_build (n := n) (mem_filter.mp hτ).2
  have hL := col_build_L hτ
  have hR := col_build_R hτ
  obtain ⟨u1, u2, u3, v1, v2, v3⟩ := τ
  have hc := (mem_filter.mp hτ).2
  simp only [Cn] at hc
  simp only at hL hR
  simp only [tau, Prod.mk.injEq]
  refine ⟨thr_eq_of fun r => ?_, thr_eq_of fun r => ?_, thr_eq_of fun r => ?_,
    thr_eq_of fun r => ?_, thr_eq_of fun r => ?_, thr_eq_of fun r => ?_⟩
  · rw [← thr_spec hm false (by norm_num), hL]; unfold bL; split_ifs <;> simp [rk] <;> omega
  · rw [← thr_spec hm false (by norm_num), hL]; unfold bL; split_ifs <;> simp [rk] <;> omega
  · rw [← thr_spec hm false (by norm_num), hL]; unfold bL; split_ifs <;> simp [rk] <;> omega
  · rw [← thr_spec hm true (by norm_num), hR]; unfold bR; split_ifs <;> simp [rk] <;> omega
  · rw [← thr_spec hm true (by norm_num), hR]; unfold bR; split_ifs <;> simp [rk] <;> omega
  · rw [← thr_spec hm true (by norm_num), hR]; unfold bR; split_ifs <;> simp [rk] <;> omega

theorem card_model (n : ℕ) (hn : 0 < n) :
    (open Classical in (Finset.univ.filter (fun f : Cell n → Fin 4 => Model f)).card) = (T n).card := by
  classical
  have hset : Finset.univ.filter (fun f : Cell n → Fin 4 => Model f) = (T n).image build := by
    ext f
    simp only [mem_filter, mem_univ, true_and, mem_image]
    constructor
    · intro hm
      exact ⟨tau f, tau_mem hm hn, build_tau hm⟩
    · rintro ⟨τ, hτ, rfl⟩
      exact model_build (mem_filter.mp hτ).2
  rw [hset, card_image_of_injOn]
  intro τ hτ τ' hτ' h
  rw [← tau_build (n := n) hτ, ← tau_build (n := n) hτ']
  exact congrArg tau h

/-- **A164754**: a(n) = 4n^2 - 11n + 5 for every n ≥ 3. -/
theorem A164754_formula (n : ℕ) (hn : 3 ≤ n) : (a n : ℤ) = 4 * (n : ℤ) ^ 2 - 11 * n + 5 := by
  rw [a_eq_model, card_model n (by omega)]
  exact card_T n hn
