import E13Lrat.F2
import E13Lrat.Steps2
import E13Lrat.F4p
import E13Lrat.Steps4p
import E13Lrat.F4n
import E13Lrat.Steps4n

/-
Guy, UPINT E13 (Turán): s(m, n) is the least s such that every n-colouring of [m, m + s] has a
monochromatic x + y = z (x = y allowed). `Colourable m s n` (in `lrat/E13Lrat/Cnf.lean`, the
same definition as in `E13_1.lean`): [m, m + s] has an n-colouring with no monochromatic
x + y = z. `IsS m n t`: t is the least s with ¬ Colourable m s n; `s m n` is that t (0 if none).

Checked here:
- `s_2_4 : s 2 4 = 82` (`isS_2_4`).
  Upper bound `upper_2_4`: `cnf 2 84` (the 4-colouring CNF of [2, 84] with colour-symmetry
  breaking, defined from the problem in `lrat/E13Lrat/Cnf.lean`, with the encoding lemma
  `not_colourable_of_unsat`, which proves the symmetry breaking sound) is unsatisfiable by
  `OpenProblemsLib.LRAT.unsat_of_parts`: the kernel checks that the clause store begins with
  `cnf 2 84` (`store2_cnf`), that each of the 234 612 LRAT additions is RUP (`steps2`, joined
  from the chunk theorems in `lrat/E13Lrat/A00..A11.lean`) and that the last one is the empty
  clause (`store2_last`).
  Lower bound `lower_2_4`: the explicit colouring `col2_4` of [2, 83], checked by `decide`.
- `s_4_4 : s 4 4 = 160` (`isS_4_4`). Upper bound `upper_4_4` in the same way from `cnf 4 164`,
  split on variable 35 ("12 has colour 2", literal codes 70 and 71; `unsat_of_split`) so that each
  store stays below the 2^18 entries of the store packing: `cnf 4 164 ++ [[70]]` (`store4p_cnf`,
  61 221 additions in `steps4p` from `lrat/E13Lrat/P00..P03.lean`) and `cnf 4 164 ++ [[71]]`
  (`store4n_cnf`, 200 702 additions in `steps4n` from `lrat/E13Lrat/N00..N11.lean`).
  Lower bound `lower_4_4` from `lower_m_4`: for every m ≥ 1 the colouring `col4 m` of
  [m, 41m - 1] (the Abbott-Znám step applied to the 3-colouring of `E13_1.lean`) has no
  monochromatic x + y = z, so s(m, 4) ≥ 40m.
Axioms: propext, Classical.choice, Quot.sound (no native_decide, no ofReduceBool).

Not checked here: nothing about the certificate data is trusted. The imported modules must be
compiled first (`lrat/build.sh`, which needs the LRAT files in `lrat/data/`; see
`lrat/README.md`), and this file is then checked with `tools/leancheck-mathlib.sh`.
-/

open OpenProblemsLib.LRAT E13Lrat

/-! ## The definition of s(m, n) -/

/-- `t` is the least `s` such that every `n`-colouring of [m, m + s] has a monochromatic
`x + y = z`. -/
def IsS (m n t : Nat) : Prop := ¬ Colourable m t n ∧ ∀ u, u < t → Colourable m u n

open Classical in
/-- Turán's s(m, n): the least such `s` (0 if there is none). -/
noncomputable def s (m n : Nat) : Nat :=
  if h : ∃ t, IsS m n t then Classical.choose h else 0

theorem isS_unique {m n t t' : Nat} (h : IsS m n t) (h' : IsS m n t') : t = t' := by
  rcases Nat.lt_trichotomy t t' with hl | he | hg
  · exact absurd (h'.2 t hl) h.1
  · exact he
  · exact absurd (h.2 t' hg) h'.1

theorem s_eq {m n t : Nat} (h : IsS m n t) : s m n = t := by
  have hex : ∃ t, IsS m n t := ⟨t, h⟩
  unfold s
  split
  · exact isS_unique (Classical.choose_spec ‹∃ t, IsS m n t›) h
  · exact absurd hex ‹_›

theorem colourable_mono {m t n : Nat} (h : Colourable m t n) (u : Nat) (hu : u ≤ t) :
    Colourable m u n := by
  obtain ⟨f, hf, hs⟩ := h
  exact ⟨f, hf, fun x y h1 h2 h3 => hs x y h1 h2 (by omega)⟩

theorem isS_of {m n t : Nat} (ht : 1 ≤ t) (h1 : Colourable m (t - 1) n)
    (h2 : ¬ Colourable m t n) : IsS m n t :=
  ⟨h2, fun u hu => colourable_mono h1 u (by omega)⟩

/-! ## Lower bounds: explicit colourings checked by the kernel -/

/-- No monochromatic `x + y = z` with `x = m + i`, `y = x + j`, `x + y ≤ N` under `f`. -/
def okAll (f : Nat → Nat) (m N : Nat) : Bool :=
  (List.range (N / 2 + 1 - m)).all fun i =>
    (List.range (N + 1 - 2 * (m + i))).all fun j =>
      !(f (m + i) == f (m + i + j) && f (m + i + j) == f (2 * (m + i) + j))

theorem colourable_of_ok (f : Nat → Nat) (n m s : Nat) (hf : ∀ x, f x < n)
    (h : okAll f m (m + s) = true) : Colourable m s n := by
  refine ⟨f, hf, fun x y hx hxy hz => ?_⟩
  simp only [okAll, List.all_eq_true, List.mem_range] at h
  have := h (x - m) (by omega) (y - x) (by omega)
  rw [show m + (x - m) = x by omega, show x + (y - x) = y by omega,
    show 2 * x + (y - x) = x + y by omega] at this
  simp only [Bool.not_eq_true', Bool.and_eq_false_iff, beq_eq_false_iff_ne, ne_eq] at this
  omega

/-- A 4-colouring of [2, 83] (entry x is the colour of x; found by CaDiCaL). -/
def col2_4L : List Nat :=
  [0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 0, 0, 1, 1, 1, 1, 0, 0, 3, 3, 3, 3, 3, 0, 0,
   2, 2, 2, 2, 1, 0, 0, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 0, 0, 1, 1, 1, 2, 2, 0, 0, 3, 3, 3, 3, 3,
   0, 0, 1, 1, 1, 1, 0, 0, 2, 2, 2, 2, 2, 2, 0, 2, 1, 1, 1, 1, 0, 0]

def col2_4 (x : Nat) : Nat := col2_4L.getD x 0 % 4

theorem ok2_4 : okAll col2_4 2 83 = true := by decide +kernel

theorem lower_2_4 : Colourable 2 81 4 :=
  colourable_of_ok col2_4 4 2 81 (fun _ => Nat.mod_lt _ (by omega)) ok2_4

/-- Turán's sum-free 2-colouring of [m, 5m - 1] (as in `E13_1.lean`). -/
def col2 (m x : Nat) : Nat := if x < 2 * m then 0 else if x < 4 * m then 1 else 0

/-- The 3-colouring of [m, 14m - 1] of `E13_1.lean`. -/
def col3 (m x : Nat) : Nat :=
  if x < 5 * m then col2 m x else if x < 10 * m then 2 else col2 m (x - 9 * m)

/-- The Abbott-Znám step once more: `col3` on [m, 14m), colour 3 on [14m, 28m), `col3`
shifted by 27m on [28m, 41m). -/
def col4 (m x : Nat) : Nat :=
  if x < 14 * m then col3 m x else if x < 28 * m then 3 else col3 m (x - 27 * m)

theorem col3_lt (m x : Nat) : col3 m x < 3 := by
  unfold col3 col2; (repeat' split) <;> omega

theorem col4_lt (m x : Nat) : col4 m x < 4 := by
  have := col3_lt m x
  have := col3_lt m (x - 27 * m)
  unfold col4; (repeat' split) <;> omega

/-- As `colouring3_sumfree` in `E13_1.lean`. -/
theorem colouring3_sumfree (m x y : Nat) (hx : m ≤ x) (hxy : x ≤ y) (hz : x + y < 14 * m) :
    ¬ (col3 m x = col3 m y ∧ col3 m y = col3 m (x + y)) := by
  unfold col3 col2; intro h; (repeat' split at h) <;> omega

theorem col3_sf (m x y : Nat) : m ≤ x → m ≤ y → x + y < 14 * m →
    ¬ (col3 m x = col3 m y ∧ col3 m y = col3 m (x + y)) := by
  intro hx hy hz
  rcases Nat.le_total x y with h | h
  · exact colouring3_sumfree m x y hx h hz
  · intro ⟨e1, e2⟩
    have := colouring3_sumfree m y x hy h (by omega)
    rw [Nat.add_comm y x] at this
    exact this ⟨by omega, by omega⟩

theorem colouring4_sumfree (m x y : Nat) (hx : m ≤ x) (hxy : x ≤ y) (hz : x + y < 41 * m) :
    ¬ (col4 m x = col4 m y ∧ col4 m y = col4 m (x + y)) := by
  intro ⟨e1, e2⟩
  have A := col3_sf m x y
  have B : m ≤ x → m ≤ y - 27 * m → x + (y - 27 * m) < 14 * m →
      ¬ (col3 m x = col3 m (y - 27 * m) ∧ col3 m (y - 27 * m) = col3 m (x + y - 27 * m)) := by
    intro h1 h2 h3
    have := col3_sf m x (y - 27 * m) h1 h2 h3
    rwa [show x + (y - 27 * m) = x + y - 27 * m by omega] at this
  have := col3_lt m x; have := col3_lt m y; have := col3_lt m (x + y)
  have := col3_lt m (y - 27 * m); have := col3_lt m (x + y - 27 * m)
  have := col3_lt m (x - 27 * m)
  unfold col4 at e1 e2
  (repeat' split at e1) <;> (repeat' split at e2) <;> omega

/-- s(m, 4) ≥ 40m: [m, 41m - 1] is 4-colourable. -/
theorem lower_m_4 (m : Nat) (hm : 1 ≤ m) : Colourable m (40 * m - 1) 4 :=
  ⟨col4 m, col4_lt m, fun x y hx hxy hz => colouring4_sumfree m x y hx hxy (by omega)⟩

/-! ## Upper bounds: LRAT certificates checked by the kernel -/

theorem cnf2_unsat : Unsat (cnf 2 84) :=
  unsat_of_parts (cnf 2 84) S2 6891 234612 cnf2_length store2_cnf (by decide) steps2 store2_last

theorem upper_2_4 : ¬ Colourable 2 82 4 := not_colourable_of_unsat 2 82 (by omega) cnf2_unsat

/-- Case split on variable `w`: if `F` with the unit clause `w` and `F` with the unit clause
`¬ w` are both unsatisfiable, so is `F`. -/
theorem unsat_of_split (F : List (List Nat)) (w : Nat) (h1 : Unsat (F ++ [[2 * w]]))
    (h2 : Unsat (F ++ [[2 * w + 1]])) : Unsat F := by
  intro v hv
  have e1 : litT v (2 * w) = v w := by
    unfold litT
    rw [show 2 * w / 2 = w by omega, show 2 * w % 2 = 0 by omega]
    cases v w <;> rfl
  have e2 : litT v (2 * w + 1) = !v w := by
    unfold litT
    rw [show (2 * w + 1) / 2 = w by omega, show (2 * w + 1) % 2 = 1 by omega]
    cases v w <;> rfl
  cases hw : v w
  · apply h2 v
    intro c hc
    simp only [List.mem_append, List.mem_singleton] at hc
    rcases hc with hc | rfl
    · exact hv c hc
    · simp [csat, e2, hw]
  · apply h1 v
    intro c hc
    simp only [List.mem_append, List.mem_singleton] at hc
    rcases hc with hc | rfl
    · exact hv c hc
    · simp [csat, e1, hw]

theorem cnf4p_unsat : Unsat (cnf 4 164 ++ [[70]]) :=
  unsat_of_parts _ S4p 25288 61221 cnf4p_length store4p_cnf (by decide) steps4p store4p_last

theorem cnf4n_unsat : Unsat (cnf 4 164 ++ [[71]]) :=
  unsat_of_parts _ S4n 25288 200702 cnf4n_length store4n_cnf (by decide) steps4n store4n_last

theorem cnf4_unsat : Unsat (cnf 4 164) := unsat_of_split (cnf 4 164) 35 cnf4p_unsat cnf4n_unsat

theorem upper_4_4 : ¬ Colourable 4 160 4 := not_colourable_of_unsat 4 160 (by omega) cnf4_unsat

/-! ## Main theorems -/

theorem isS_2_4 : IsS 2 4 82 := isS_of (by omega) lower_2_4 upper_2_4

/-- Turán's s(2, 4) = 82. -/
theorem s_2_4 : s 2 4 = 82 := s_eq isS_2_4

theorem lower_4_4 : Colourable 4 159 4 := lower_m_4 4 (by omega)

theorem isS_4_4 : IsS 4 4 160 := isS_of (by omega) lower_4_4 upper_4_4

/-- Turán's s(4, 4) = 160. -/
theorem s_4_4 : s 4 4 = 160 := s_eq isS_4_4
