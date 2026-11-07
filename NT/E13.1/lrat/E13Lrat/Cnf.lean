import OpenProblemsLib.LRAT

/-!
# NT-E13.1: the symmetry-broken CNF for 4-colourings of [m, N], defined from the problem

`Colourable m s n` (as in `../../E13_1.lean`): some colouring `f` with colours `< n` has no
monochromatic `x + y = z` (`x = y` allowed) with `m ≤ x ≤ y`, `x + y ≤ m + s`.

`cnf m N` has the variable `4 (x - m) + c + 1` for "x has colour c" (`x ∈ [m, N]`, `c < 4`;
literal codes `2 v` positive, `2 v + 1` negative, see `OpenProblemsLib.LRAT.litT`), in the
order of `../cnf.py`:
1. `alo`: every `x` has some colour;
2. `triples`: for `m ≤ x ≤ y`, `x + y ≤ N` and every colour `c`, not all of `x, y, x + y` have
   colour `c` (two literals when `x = y`);
3. `symm` (colour-symmetry breaking): `m` has colour 0, `2m` has colour 1, and for
   `m < i ≤ N`, if `i` has colour 3 then some `j ∈ [m, i)` has colour 2.

Checked: `sat_of_colourable` (every colouring of [m, N] without a monochromatic triple can be
recoloured by a permutation of the 4 colours into one satisfying `cnf m N`, so the symmetry
breaking is sound) and `not_colourable_of_unsat` (so `Unsat (cnf m (m + s))` gives
`¬ Colourable m s 4`). Axioms propext, Classical.choice, Quot.sound at most.
-/

namespace E13Lrat

open OpenProblemsLib.LRAT

/-- [m, m + s] has an n-colouring (colours < n) with no monochromatic x + y = z. -/
def Colourable (m s n : Nat) : Prop :=
  ∃ f : Nat → Nat, (∀ x, f x < n) ∧
    ∀ x y, m ≤ x → x ≤ y → x + y ≤ m + s → ¬ (f x = f y ∧ f y = f (x + y))

/-- The variable "x has colour c". -/
def var (m x c : Nat) : Nat := 4 * (x - m) + c + 1

/-- Literal "x has colour c". -/
def pos (m x c : Nat) : Nat := 2 * var m x c

/-- Literal "x does not have colour c". -/
def neg (m x c : Nat) : Nat := 2 * var m x c + 1

/-- Every x in [m, N] has a colour. -/
def alo (m N : Nat) : List (List Nat) :=
  (List.range (N + 1 - m)).map fun i =>
    [pos m (m + i) 0, pos m (m + i) 1, pos m (m + i) 2, pos m (m + i) 3]

/-- No monochromatic x + y = z with x = m + i, y = x + j. -/
def triples (m N : Nat) : List (List Nat) :=
  (List.range (N / 2 + 1 - m)).flatMap fun i =>
    (List.range (N + 1 - 2 * (m + i))).flatMap fun j =>
      (List.range 4).map fun c =>
        if j = 0 then [neg m (m + i) c, neg m (2 * (m + i)) c]
        else [neg m (m + i) c, neg m (m + i + j) c, neg m (2 * (m + i) + j) c]

/-- Symmetry breaking: m has colour 0, 2m colour 1, colour 3 only after colour 2. -/
def symm (m N : Nat) : List (List Nat) :=
  [pos m m 0] :: [pos m (2 * m) 1] :: (List.range (N - m)).map fun i =>
    neg m (m + 1 + i) 3 :: (List.range (i + 1)).map fun j => pos m (m + j) 2

def cnf (m N : Nat) : List (List Nat) := alo m N ++ triples m N ++ symm m N

/-! ## Recolouring -/

theorem least_of_exists (P : Nat → Prop) (k : Nat) (hk : P k) :
    ∃ k, P k ∧ ∀ j, j < k → ¬ P j := by
  induction k using Nat.strongRecOn with
  | _ k ih =>
    by_cases h : ∃ j, j < k ∧ P j
    · obtain ⟨j, hj, hPj⟩ := h
      exact ih j hj hPj
    · exact ⟨k, hk, fun j hj hPj => h ⟨j, hj, hPj⟩⟩

/-- Colour `d`, distinct from `a` and `b`, that first appears before any colour outside
`{a, b, d}`. -/
theorem first_new (f : Nat → Nat) (hf : ∀ x, f x < 4) (m N a b : Nat) :
    ∃ d, d < 4 ∧ d ≠ a ∧ d ≠ b ∧ ∀ i, m ≤ i → i ≤ N → f i ≠ a → f i ≠ b → f i ≠ d →
      ∃ j, m ≤ j ∧ j < i ∧ f j = d := by
  by_cases hex : ∃ k, m ≤ k ∧ k ≤ N ∧ f k ≠ a ∧ f k ≠ b
  · obtain ⟨k, hk⟩ := hex
    obtain ⟨k0, ⟨h1, _, h3, h4⟩, hmin⟩ :=
      least_of_exists (fun k => m ≤ k ∧ k ≤ N ∧ f k ≠ a ∧ f k ≠ b) k hk
    refine ⟨f k0, hf k0, h3, h4, fun i hi1 hi2 hia hib hid => ⟨k0, h1, ?_, rfl⟩⟩
    have : ¬ i < k0 := fun hlt => hmin i hlt ⟨hi1, hi2, hia, hib⟩
    have : i ≠ k0 := fun he => hid (he ▸ rfl)
    omega
  · have hd : ∃ d, d < 4 ∧ d ≠ a ∧ d ≠ b := by
      by_cases h0 : a = 0 ∨ b = 0
      · by_cases h1 : a = 1 ∨ b = 1
        · exact ⟨2, by omega, by omega, by omega⟩
        · exact ⟨1, by omega, by omega, by omega⟩
      · exact ⟨0, by omega, by omega, by omega⟩
    obtain ⟨d, hd1, hd2, hd3⟩ := hd
    exact ⟨d, hd1, hd2, hd3, fun i hi1 hi2 hia hib _ => absurd ⟨i, hi1, hi2, hia, hib⟩ hex⟩

/-- The colouring `f` with colours renamed `a ↦ 0`, `b ↦ 1`, `d ↦ 2`, the fourth `↦ 3`. -/
def recol (f : Nat → Nat) (a b d x : Nat) : Nat :=
  if f x = a then 0 else if f x = b then 1 else if f x = d then 2 else 3

theorem recol_lt (f : Nat → Nat) (a b d x : Nat) : recol f a b d x < 4 := by
  unfold recol; (repeat' split) <;> omega

/-- Renaming is injective on colours `< 4`. -/
theorem recol_inj (f : Nat → Nat) (hf : ∀ x, f x < 4) (a b d x y : Nat) (ha : a < 4)
    (hb : b < 4) (hd : d < 4) (_hab : a ≠ b) (hda : d ≠ a) (hdb : d ≠ b)
    (h : recol f a b d x = recol f a b d y) : f x = f y := by
  have := hf x; have := hf y
  unfold recol at h; (repeat' split at h) <;> omega

theorem recol_three (f : Nat → Nat) (a b d x : Nat) (h : recol f a b d x = 3) :
    f x ≠ a ∧ f x ≠ b ∧ f x ≠ d := by
  unfold recol at h; (repeat' split at h) <;> omega

/-! ## The valuation of a colouring -/

/-- Variable `w = 4 (x - m) + c + 1` is true iff `g x = c`. -/
def val (m : Nat) (g : Nat → Nat) (w : Nat) : Bool := g (m + (w - 1) / 4) == (w - 1) % 4

theorem litT_pos (m : Nat) (g : Nat → Nat) (x c : Nat) (hx : m ≤ x) (hc : c < 4) :
    litT (val m g) (pos m x c) = (g x == c) := by
  unfold litT pos var val
  rw [show 2 * (4 * (x - m) + c + 1) / 2 = 4 * (x - m) + c + 1 by omega,
    show 2 * (4 * (x - m) + c + 1) % 2 = 0 by omega,
    show (4 * (x - m) + c + 1 - 1) / 4 = x - m by omega,
    show (4 * (x - m) + c + 1 - 1) % 4 = c by omega, show m + (x - m) = x by omega]
  cases (g x == c) <;> rfl

theorem litT_neg (m : Nat) (g : Nat → Nat) (x c : Nat) (hx : m ≤ x) (hc : c < 4) :
    litT (val m g) (neg m x c) = !(g x == c) := by
  unfold litT neg var val
  rw [show (2 * (4 * (x - m) + c + 1) + 1) / 2 = 4 * (x - m) + c + 1 by omega,
    show (2 * (4 * (x - m) + c + 1) + 1) % 2 = 1 by omega,
    show (4 * (x - m) + c + 1 - 1) / 4 = x - m by omega,
    show (4 * (x - m) + c + 1 - 1) % 4 = c by omega, show m + (x - m) = x by omega]
  cases (g x == c) <;> rfl

/-- A colouring of [m, N] in the symmetry-broken form satisfies `cnf m N`. -/
theorem sat_of_broken (m N : Nat) (g : Nat → Nat) (hg : ∀ x, g x < 4)
    (hsf : ∀ x y, m ≤ x → x ≤ y → x + y ≤ N → ¬ (g x = g y ∧ g y = g (x + y)))
    (h0 : g m = 0) (h1 : g (2 * m) = 1)
    (h3 : ∀ i, m < i → i ≤ N → g i = 3 → ∃ j, m ≤ j ∧ j < i ∧ g j = 2) :
    Satisfies (val m g) (cnf m N) := by
  intro cl hcl
  simp only [cnf, List.mem_append] at hcl
  rcases hcl with (h | h) | h
  · simp only [alo, List.mem_map, List.mem_range] at h
    obtain ⟨i, _, rfl⟩ := h
    simp only [csat, List.any_cons, List.any_nil, Bool.or_false]
    rw [litT_pos m g (m + i) 0 (by omega) (by omega), litT_pos m g (m + i) 1 (by omega) (by omega),
      litT_pos m g (m + i) 2 (by omega) (by omega), litT_pos m g (m + i) 3 (by omega) (by omega)]
    have := hg (m + i)
    simp only [Bool.or_eq_true, beq_iff_eq]
    omega
  · simp only [triples, List.mem_flatMap, List.mem_range, List.mem_map] at h
    obtain ⟨i, hi, j, hj, c, hc, rfl⟩ := h
    split
    · rename_i hj0
      simp only [csat, List.any_cons, List.any_nil, Bool.or_false]
      rw [litT_neg m g (m + i) c (by omega) hc, litT_neg m g (2 * (m + i)) c (by omega) hc]
      have := hsf (m + i) (m + i) (by omega) (Nat.le_refl _) (by omega)
      rw [show m + i + (m + i) = 2 * (m + i) by omega] at this
      simp only [Bool.or_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq]
      omega
    · simp only [csat, List.any_cons, List.any_nil, Bool.or_false]
      rw [litT_neg m g (m + i) c (by omega) hc, litT_neg m g (m + i + j) c (by omega) hc,
        litT_neg m g (2 * (m + i) + j) c (by omega) hc]
      have := hsf (m + i) (m + i + j) (by omega) (by omega) (by omega)
      rw [show m + i + (m + i + j) = 2 * (m + i) + j by omega] at this
      simp only [Bool.or_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq]
      omega
  · simp only [symm, List.mem_cons, List.mem_map, List.mem_range] at h
    rcases h with rfl | rfl | ⟨i, hi, rfl⟩
    · simp only [csat, List.any_cons, List.any_nil, Bool.or_false]
      rw [litT_pos m g m 0 (Nat.le_refl _) (by omega), h0]; rfl
    · simp only [csat, List.any_cons, List.any_nil, Bool.or_false]
      rw [litT_pos m g (2 * m) 1 (by omega) (by omega), h1]; rfl
    · simp only [csat, List.any_cons, Bool.or_eq_true]
      rw [litT_neg m g (m + 1 + i) 3 (by omega) (by omega)]
      by_cases hg3 : g (m + 1 + i) = 3
      · obtain ⟨j, hj1, hj2, hj3⟩ := h3 (m + 1 + i) (by omega) (by omega) hg3
        right
        rw [List.any_eq_true]
        refine ⟨pos m j 2, List.mem_map.mpr ⟨j - m, List.mem_range.mpr (by omega), ?_⟩, ?_⟩
        · rw [show m + (j - m) = j by omega]
        · rw [litT_pos m g j 2 hj1 (by omega), hj3]; rfl
      · left
        simp only [Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq]
        exact hg3

/-- Encoding lemma: `Unsat (cnf m (m + s))` gives `¬ Colourable m s 4`. Every colouring is
first renamed into the symmetry-broken form (`recol`, with `first_new`). -/
theorem not_colourable_of_unsat (m s : Nat) (hms : m ≤ s) (hu : Unsat (cnf m (m + s))) :
    ¬ Colourable m s 4 := by
  rintro ⟨f, hf, hsf⟩
  have hab : f m ≠ f (2 * m) := by
    intro he
    apply hsf m m (Nat.le_refl _) (Nat.le_refl _) (by omega)
    rw [show m + m = 2 * m by omega]
    exact ⟨rfl, he⟩
  obtain ⟨d, hd4, hda, hdb, hd⟩ := first_new f hf m (m + s) (f m) (f (2 * m))
  apply hu (val m (recol f (f m) (f (2 * m)) d))
  apply sat_of_broken m (m + s) _ (recol_lt f _ _ d)
  · intro x y hx hxy hz ⟨e1, e2⟩
    exact hsf x y hx hxy hz ⟨recol_inj f hf _ _ d x y (hf _) (hf _) hd4 hab hda hdb e1,
      recol_inj f hf _ _ d y (x + y) (hf _) (hf _) hd4 hab hda hdb e2⟩
  · unfold recol; simp
  · unfold recol; simp [Ne.symm hab]
  · intro i hi1 hi2 hgi
    obtain ⟨ea, eb, ed⟩ := recol_three f _ _ d i hgi
    obtain ⟨j, hj1, hj2, hj3⟩ := hd i (by omega) hi2 ea eb ed
    refine ⟨j, hj1, hj2, ?_⟩
    unfold recol
    rw [hj3]
    simp [hda, hdb]

end E13Lrat
