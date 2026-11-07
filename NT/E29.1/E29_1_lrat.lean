import E29Lrat.F
import E29Lrat.Steps

/-
NT-E29.1 (Guy E29, Graham's question), interval starting at 3: the threshold is exactly 3150.

Checked here (`forces_iff`): for every N, every 2-colouring has x < y with x ≥ 3, x·y ≤ N and
x, y, x + y, x·y of one colour (`E29Lrat.Forces N`) iff N ≥ 3150.
- Upper bound `forces_3150`: `cnf 3150` (defined from the problem in `lrat/E29Lrat/Cnf.lean`,
  with the encoding lemma `forces_of_unsat`) is unsatisfiable by `OpenProblemsLib.LRAT.unsat_of_parts`:
  the kernel checks that the clause store begins with `cnf 3150` (`store_cnf`), that each of the
  126 702 LRAT additions is RUP (`steps_all`, joined from 375 chunk theorems in
  `lrat/E29Lrat/C00..C07.lean`) and that the last one is the empty clause (`store_last`).
- Lower bound `not_forces_3149`: the explicit colouring below (copied from `E29_1.lean`).
Axioms: propext, Classical.choice, Quot.sound (no native_decide, no ofReduceBool).

Not checked here: nothing about the certificate data is trusted. The imported modules must be
compiled first (`lrat/build.sh`, which needs the LRAT file `lrat/data/e29.lrat`; see
`lrat/README.md`), and this file is then checked with `tools/leancheck-mathlib.sh`.
-/

open OpenProblemsLib.LRAT E29Lrat

theorem cnf_unsat : Unsat (cnf 3150) :=
  unsat_of_parts (cnf 3150) S 16378 126702 cnf_length store_cnf (by decide) steps_all store_last

theorem forces_3150 : Forces 3150 := forces_of_unsat 3150 cnf_unsat

/-- The colouring as the bits of one natural number: bit n is the colour of n. -/
def C : Nat := 1511135755451182382973686691344305305948072201132108124561771039531090446871060037198272766219951367718551468716898878533559606171767370577346917687303116151744548071222070502758178250175472713003543153120715616091591873164689974948080729854713841772921159764922138719066405828071476942295172089347438947241785676486983605589543569031651935190586184124393157824048506621341807815642598970437227988897517449017666815863472588666699277449026580201658327489513190219230504217015159828888291013540924198579837967796873529408492851890251725393783421984703888358345181353049524028576815088809203131457381890584670361458739139442811456943521255236510977193533313032331931734028727051725506298788676193660398942589006467968526877057669000850611850210341585003197921193315065939093388428206468356345450566794987294894418580470161017659729434936707441050688755574877417114672387440687967604176025542009361013406706814276902519563263415051238157304882113718952

def colour (n : Nat) : Bool := (C >>> n) % 2 == 1

def mono (x y : Nat) : Bool :=
  colour x == colour y && colour y == colour (x + y) && colour (x + y) == colour (x * y)

/-- `rowOk x k`: no monochromatic quadruple for y = x+1, ..., x+k. -/
def rowOk (x : Nat) : Nat → Bool
  | 0 => true
  | k + 1 => !mono x (x + k + 1) && rowOk x k

/-- `allOk i`: rows x = 3, ..., i + 2, each up to y = 3149 / x. -/
def allOk : Nat → Bool
  | 0 => true
  | i + 1 => rowOk (i + 3) (3149 / (i + 3) - (i + 3)) && allOk i

theorem allOk_53 : allOk 53 = true := by decide +kernel

theorem rowOk_spec (x : Nat) : ∀ k, rowOk x k = true → ∀ j, 1 ≤ j → j ≤ k → mono x (x + j) = false := by
  intro k
  induction k with
  | zero => intro _ j h1 h2; omega
  | succ k ih =>
    intro h j h1 h2
    simp only [rowOk, Bool.and_eq_true, Bool.not_eq_true'] at h
    by_cases hj : j = k + 1
    · subst hj; simpa [Nat.add_assoc] using h.1
    · exact ih h.2 j h1 (by omega)

theorem allOk_spec : ∀ i, allOk i = true → ∀ x, 3 ≤ x → x < i + 3 → rowOk x (3149 / x - x) = true := by
  intro i
  induction i with
  | zero => intro _ x h1 h2; omega
  | succ i ih =>
    intro h x h1 h2
    simp only [allOk, Bool.and_eq_true] at h
    by_cases hx : x = i + 3
    · subst hx; exact h.1
    · exact ih h.2 x h1 (by omega)

/-- No monochromatic x < y, x + y, x·y inside [3, 3149] under `colour`. -/
theorem no_mono (x y : Nat) (hx : 3 ≤ x) (hxy : x < y) (hp : x * y ≤ 3149) :
    ¬ (colour x = colour y ∧ colour y = colour (x + y) ∧ colour (x + y) = colour (x * y)) := by
  have hx56 : x < 56 := by
    rcases Nat.lt_or_ge x 56 with h | h
    · exact h
    · have : 56 * 57 ≤ x * y := Nat.mul_le_mul h (by omega)
      omega
  have hrow := allOk_spec 53 allOk_53 x hx (by omega)
  have hy : y ≤ 3149 / x := (Nat.le_div_iff_mul_le (by omega)).mpr (by rw [Nat.mul_comm]; exact hp)
  have hm := rowOk_spec x _ hrow (y - x) (by omega) (by omega)
  have hyx : x + (y - x) = y := by omega
  rw [hyx] at hm
  intro ⟨h1, h2, h3⟩
  simp [mono, h1, h2, h3] at hm

theorem not_forces_3149 : ¬ Forces 3149 := by
  intro h
  obtain ⟨x, y, h1, h2, h3, hm⟩ := h colour
  exact no_mono x y h1 h2 h3 hm

theorem forces_mono {N N' : Nat} (hN : N ≤ N') (h : Forces N) : Forces N' := by
  intro c
  obtain ⟨x, y, h1, h2, h3, hm⟩ := h c
  exact ⟨x, y, h1, h2, by omega, hm⟩

/-- The threshold for the interval starting at 3 is exactly 3150. -/
theorem forces_iff (N : Nat) : Forces N ↔ 3150 ≤ N := by
  constructor
  · intro h
    apply Classical.byContradiction
    intro hN
    exact not_forces_3149 (forces_mono (by omega) h)
  · intro hN
    exact forces_mono hN forces_3150
