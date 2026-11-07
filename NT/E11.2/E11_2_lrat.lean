import E11Lrat.F
import E11Lrat.Steps

/-
Guy, UPINT E11 (generalized Schur numbers): σ(m, n) is the least v such that every n-colouring
of [1, v] has a monochromatic solution of a_1 + … + a_{m-1} = a_m (a_i not necessarily
distinct). Here m = 4 (x + y + z = w) and n = 4 colours.

`Colourable N n` (in `lrat/E11Lrat/Cnf.lean`): [1, N] has an n-colouring with no monochromatic
x + y + z = w, 1 ≤ x ≤ y ≤ z, w = x + y + z ≤ N. `IsSigma n t`: t is the least N with
¬ Colourable N n; `sigma4 n` is that t (0 if none).

Main theorem `sigma4_4 : sigma4 4 = 171` (from `isSigma_4_171`), i.e. σ(4, 4) = 171 = 4^4 - 4^3 - 4^2 - 4 - 1.
- Lower bound `lower`: the explicit colouring `col170` of [1, 170] (found by CaDiCaL), checked
  by `decide` over all solutions with w ≤ 170.
- Upper bound `upper`: `cnf 171 L` (4-colouring CNF of [1, 171] with colour-symmetry breaking,
  defined in `lrat/E11Lrat/Cnf.lean`; L = the 44 526 solution clauses the proof uses, each checked
  to be a genuine solution by `L_valid`) is unsatisfiable by
  `OpenProblemsLib.LRAT.unsat_of_parts`: the kernel checks that the clause store begins with
  `cnf 171 L` (`store_cnf`), that each of the 187 512 LRAT additions is RUP (`stepsAll`, joined
  from `lrat/E11Lrat/Q00..Q10.lean`) and that the last is the empty clause (`store_last`).
  The encoding lemma `not_colourable_of_unsat` proves the symmetry breaking sound and holds
  for any list of valid solution tuples.
Axioms: propext, Classical.choice, Quot.sound (no native_decide, no ofReduceBool).
Not checked here: nothing about the certificate data is trusted. The imported modules must be
compiled first (`lrat/build.sh`, which needs the files in `lrat/data/`; see `lrat/README.md`).
-/

open OpenProblemsLib.LRAT E11Lrat

/-- t is the least N such that every n-colouring of [1, N] has a monochromatic x + y + z = w. -/
def IsSigma (n t : Nat) : Prop := ¬ Colourable t n ∧ ∀ u, u < t → Colourable u n

open Classical in
/-- Guy's σ(4, n): the least such t (0 if there is none). -/
noncomputable def sigma4 (n : Nat) : Nat :=
  if h : ∃ t, IsSigma n t then Classical.choose h else 0

theorem isSigma_unique {n t t' : Nat} (h : IsSigma n t) (h' : IsSigma n t') : t = t' := by
  rcases Nat.lt_trichotomy t t' with hl | he | hg
  · exact absurd (h'.2 t hl) h.1
  · exact he
  · exact absurd (h.2 t' hg) h'.1

theorem sigma4_eq {n t : Nat} (h : IsSigma n t) : sigma4 n = t := by
  have hex : ∃ t, IsSigma n t := ⟨t, h⟩
  unfold sigma4
  split
  · exact isSigma_unique (Classical.choose_spec ‹∃ t, IsSigma n t›) h
  · exact absurd hex ‹_›

theorem colourable_mono {N n : Nat} (h : Colourable N n) (u : Nat) (hu : u ≤ N) :
    Colourable u n := by
  obtain ⟨f, hf, hs⟩ := h
  exact ⟨f, hf, fun x y z h1 h2 h3 h4 => hs x y z h1 h2 h3 (by omega)⟩

/-! ## Lower bound: an explicit colouring checked by the kernel -/

/-- No monochromatic x + y + z = w with x = i + 1, y = x + j, z = y + k, w ≤ N under f. -/
def okAll (f : Nat → Nat) (N : Nat) : Bool :=
  (List.range (N / 3)).all fun i =>
    (List.range ((N - (i + 1)) / 2 + 1 - (i + 1))).all fun j =>
      (List.range (N - (i + 1) - (i + 1 + j) + 1 - (i + 1 + j))).all fun k =>
        !(f (i + 1) == f (i + 1 + j) && f (i + 1 + j) == f (i + 1 + j + k) &&
          f (i + 1 + j + k) == f (i + 1 + (i + 1 + j) + (i + 1 + j + k)))

theorem colourable_of_ok (f : Nat → Nat) (n N : Nat) (hf : ∀ x, f x < n)
    (h : okAll f N = true) : Colourable N n := by
  refine ⟨f, hf, fun x y z hx hxy hyz hw => ?_⟩
  simp only [okAll, List.all_eq_true, List.mem_range] at h
  have := h (x - 1) (by omega) (y - x) (by omega) (z - y) (by omega)
  rw [show x - 1 + 1 = x by omega, show x + (y - x) = y by omega,
    show y + (z - y) = z by omega] at this
  simp only [Bool.not_eq_true', Bool.and_eq_false_iff, beq_eq_false_iff_ne, ne_eq] at this
  omega

/-- A 4-colouring of [1, 170]: entry x - 1 is the colour of x (found by CaDiCaL). -/
def col170L : List Nat :=
  [0, 0, 1, 1, 1, 1, 1, 1, 0, 0, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 0, 0, 1, 1, 1, 1, 1, 1, 0, 0, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 0, 0, 1, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 0, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 1, 3, 3, 3, 3, 3, 0, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 0, 3, 3, 3, 3, 3, 3, 3, 0, 0, 1, 1, 1, 1, 1, 1, 0, 0, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 0, 2, 2, 2, 2, 2, 2, 2, 0, 0, 1, 1, 1, 1, 1, 1, 0, 0]

def col170 (x : Nat) : Nat := col170L.getD (x - 1) 0 % 4

theorem ok170 : okAll col170 170 = true := by decide +kernel

theorem lower : Colourable 170 4 :=
  colourable_of_ok col170 4 170 (fun _ => Nat.mod_lt _ (by omega)) ok170

/-! ## Upper bound: the LRAT certificate -/

theorem cnf_unsat : Unsat (cnf 171 L) :=
  unsat_of_parts (cnf 171 L) S 45895 187512 cnf_length store_cnf (by decide) stepsAll store_last

theorem upper : ¬ Colourable 171 4 := not_colourable_of_unsat 171 (by omega) L L_valid cnf_unsat

/-! ## Main theorem -/

theorem isSigma_4_171 : IsSigma 4 171 :=
  ⟨upper, fun u hu => colourable_mono lower u (by omega)⟩

/-- σ(4, 4) = 171. -/
theorem sigma4_4 : sigma4 4 = 171 := sigma4_eq isSigma_4_171
