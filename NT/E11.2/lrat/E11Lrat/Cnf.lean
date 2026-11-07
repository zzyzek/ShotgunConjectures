import OpenProblemsLib.LRAT

/-!
# NT-E11.2: the CNF for 4-colourings of [1, N] without a monochromatic x + y + z = w

`Colourable N n`: some colouring `f` with colours `< n` has no monochromatic solution of
`x + y + z = w` with `1 ≤ x ≤ y ≤ z` and `w = x + y + z ≤ N` (repeats allowed). Guy's generalized
Schur number σ(4, n) is the least N with `¬ Colourable N n`.

`cnf N L` has the variable `4 (x - 1) + c + 1` for "x has colour c" (`x ∈ [1, N]`, `c < 4`;
literal codes `2 v` positive, `2 v + 1` negative, see `OpenProblemsLib.LRAT.litT`), in the
order of `../gen2.py` (certificate/gen2.py):
1. `alo`: every `x` has some colour;
2. `amo`: no `x` has two colours;
3. `symm` (colour-symmetry breaking): 1 has colour 0, 3 has colour 1, and for `2 ≤ i ≤ N`,
   if `i` has colour 3 then some `j ∈ [1, i)` has colour 2;
4. `L.map triC`: for each listed `(x, y, z, c)`, not all of `x, y, z, x + y + z` have colour `c`
   (repeated numbers listed once). `L` is any list of valid tuples (`validT`); the file
   `Tri.lean` gives the one used (a subset of all solutions: the clauses the SAT proof needs).

Checked: `sat_of_broken` (a colouring in symmetry-broken form satisfies `cnf N L` for every list
`L` of valid tuples) and `not_colourable_of_unsat` (every colouring is recoloured by a permutation
of the 4 colours into that form, so `Unsat (cnf N L)` gives `¬ Colourable N 4`).
Axioms propext, Classical.choice, Quot.sound at most.
-/

namespace E11Lrat

open OpenProblemsLib.LRAT

/-- [1, N] has an n-colouring (colours < n) with no monochromatic x + y + z = w. -/
def Colourable (N n : Nat) : Prop :=
  ∃ f : Nat → Nat, (∀ x, f x < n) ∧
    ∀ x y z, 1 ≤ x → x ≤ y → y ≤ z → x + y + z ≤ N →
      ¬ (f x = f y ∧ f y = f z ∧ f z = f (x + y + z))

/-- The variable "x has colour c". -/
def var (x c : Nat) : Nat := 4 * (x - 1) + c + 1

/-- Literal "x has colour c". -/
def pos (x c : Nat) : Nat := 2 * var x c

/-- Literal "x does not have colour c". -/
def neg (x c : Nat) : Nat := 2 * var x c + 1

/-- Every x in [1, N] has a colour. -/
def alo (N : Nat) : List (List Nat) :=
  (List.range N).map fun i => [pos (1 + i) 0, pos (1 + i) 1, pos (1 + i) 2, pos (1 + i) 3]

/-- No x in [1, N] has two colours. -/
def amo (N : Nat) : List (List Nat) :=
  (List.range N).flatMap fun i =>
    [[neg (1 + i) 0, neg (1 + i) 1], [neg (1 + i) 0, neg (1 + i) 2],
     [neg (1 + i) 0, neg (1 + i) 3], [neg (1 + i) 1, neg (1 + i) 2],
     [neg (1 + i) 1, neg (1 + i) 3], [neg (1 + i) 2, neg (1 + i) 3]]

/-- Symmetry breaking: 1 has colour 0, 3 colour 1, colour 3 only after colour 2. -/
def symm (N : Nat) : List (List Nat) :=
  [pos 1 0] :: [pos 3 1] :: (List.range (N - 1)).map fun i =>
    neg (2 + i) 3 :: (List.range (i + 1)).map fun j => pos (1 + j) 2

/-- The clause "x, y, z, x + y + z do not all have colour c" (repeats removed). -/
def triC (t : Nat × Nat × Nat × Nat) : List Nat :=
  match t with
  | (x, y, z, c) =>
    if x = y ∧ y = z then [neg x c, neg (x + y + z) c]
    else if x = y then [neg x c, neg z c, neg (x + y + z) c]
    else if y = z then [neg x c, neg y c, neg (x + y + z) c]
    else [neg x c, neg y c, neg z c, neg (x + y + z) c]

/-- A tuple `(x, y, z, c)` names a solution in [1, N] and a colour. -/
def validT (N : Nat) (t : Nat × Nat × Nat × Nat) : Bool :=
  match t with
  | (x, y, z, c) => decide (1 ≤ x) && decide (x ≤ y) && decide (y ≤ z) &&
      decide (x + y + z ≤ N) && decide (c < 4)

def cnf (N : Nat) (L : List (Nat × Nat × Nat × Nat)) : List (List Nat) :=
  alo N ++ amo N ++ symm N ++ L.map triC

/-! ## Recolouring (as in NT-E13.1) -/

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

/-- Variable `w = 4 (x - 1) + c + 1` is true iff `g x = c`. -/
def val (g : Nat → Nat) (w : Nat) : Bool := g (1 + (w - 1) / 4) == (w - 1) % 4

theorem litT_pos (g : Nat → Nat) (x c : Nat) (hx : 1 ≤ x) (hc : c < 4) :
    litT (val g) (pos x c) = (g x == c) := by
  unfold litT pos var val
  rw [show 2 * (4 * (x - 1) + c + 1) / 2 = 4 * (x - 1) + c + 1 by omega,
    show 2 * (4 * (x - 1) + c + 1) % 2 = 0 by omega,
    show (4 * (x - 1) + c + 1 - 1) / 4 = x - 1 by omega,
    show (4 * (x - 1) + c + 1 - 1) % 4 = c by omega, show 1 + (x - 1) = x by omega]
  cases (g x == c) <;> rfl

theorem litT_neg (g : Nat → Nat) (x c : Nat) (hx : 1 ≤ x) (hc : c < 4) :
    litT (val g) (neg x c) = !(g x == c) := by
  unfold litT neg var val
  rw [show (2 * (4 * (x - 1) + c + 1) + 1) / 2 = 4 * (x - 1) + c + 1 by omega,
    show (2 * (4 * (x - 1) + c + 1) + 1) % 2 = 1 by omega,
    show (4 * (x - 1) + c + 1 - 1) / 4 = x - 1 by omega,
    show (4 * (x - 1) + c + 1 - 1) % 4 = c by omega, show 1 + (x - 1) = x by omega]
  cases (g x == c) <;> rfl

/-- A colouring of [1, N] in the symmetry-broken form satisfies `cnf N L`. -/
theorem sat_of_broken (N : Nat) (L : List (Nat × Nat × Nat × Nat))
    (hL : L.all (validT N) = true) (g : Nat → Nat) (hg : ∀ x, g x < 4)
    (hsf : ∀ x y z, 1 ≤ x → x ≤ y → y ≤ z → x + y + z ≤ N →
      ¬ (g x = g y ∧ g y = g z ∧ g z = g (x + y + z)))
    (h0 : g 1 = 0) (h1 : g 3 = 1)
    (h3 : ∀ i, 1 < i → i ≤ N → g i = 3 → ∃ j, 1 ≤ j ∧ j < i ∧ g j = 2) :
    Satisfies (val g) (cnf N L) := by
  intro cl hcl
  simp only [cnf, List.mem_append] at hcl
  rcases hcl with ((h | h) | h) | h
  · simp only [alo, List.mem_map, List.mem_range] at h
    obtain ⟨i, _, rfl⟩ := h
    simp only [csat, List.any_cons, List.any_nil, Bool.or_false]
    rw [litT_pos g (1 + i) 0 (by omega) (by omega), litT_pos g (1 + i) 1 (by omega) (by omega),
      litT_pos g (1 + i) 2 (by omega) (by omega), litT_pos g (1 + i) 3 (by omega) (by omega)]
    have := hg (1 + i)
    simp only [Bool.or_eq_true, beq_iff_eq]
    omega
  · simp only [amo, List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil,
      or_false] at h
    obtain ⟨i, _, h⟩ := h
    have := hg (1 + i)
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;>
    · simp only [csat, List.any_cons, List.any_nil, Bool.or_false]
      rw [litT_neg g (1 + i) _ (by omega) (by omega), litT_neg g (1 + i) _ (by omega) (by omega)]
      simp only [Bool.or_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq]
      omega
  · simp only [symm, List.mem_cons, List.mem_map, List.mem_range] at h
    rcases h with rfl | rfl | ⟨i, hi, rfl⟩
    · simp only [csat, List.any_cons, List.any_nil, Bool.or_false]
      rw [litT_pos g 1 0 (Nat.le_refl _) (by omega), h0]; rfl
    · simp only [csat, List.any_cons, List.any_nil, Bool.or_false]
      rw [litT_pos g 3 1 (by omega) (by omega), h1]; rfl
    · simp only [csat, List.any_cons, Bool.or_eq_true]
      rw [litT_neg g (2 + i) 3 (by omega) (by omega)]
      by_cases hg3 : g (2 + i) = 3
      · obtain ⟨j, hj1, hj2, hj3⟩ := h3 (2 + i) (by omega) (by omega) hg3
        right
        rw [List.any_eq_true]
        refine ⟨pos j 2, List.mem_map.mpr ⟨j - 1, List.mem_range.mpr (by omega), ?_⟩, ?_⟩
        · rw [show 1 + (j - 1) = j by omega]
        · rw [litT_pos g j 2 hj1 (by omega), hj3]; rfl
      · left
        simp only [Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq]
        exact hg3
  · simp only [List.mem_map] at h
    obtain ⟨⟨x, y, z, c⟩, ht, rfl⟩ := h
    have hv := List.all_eq_true.mp hL _ ht
    simp only [validT, Bool.and_eq_true, decide_eq_true_eq] at hv
    obtain ⟨⟨⟨⟨hx, hxy⟩, hyz⟩, hw⟩, hc⟩ := hv
    have hs := hsf x y z hx hxy hyz hw
    have ln := fun u (hu : 1 ≤ u) => litT_neg g u c hu hc
    simp only [triC]
    split
    · rename_i he
      simp only [csat, List.any_cons, List.any_nil, Bool.or_false]
      rw [ln x hx, ln (x + y + z) (by omega)]
      simp only [Bool.or_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq]
      obtain ⟨rfl, rfl⟩ := he
      omega
    · split
      · rename_i _ he
        simp only [csat, List.any_cons, List.any_nil, Bool.or_false]
        rw [ln x hx, ln z (by omega), ln (x + y + z) (by omega)]
        simp only [Bool.or_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq]
        subst he
        omega
      · split
        · rename_i _ _ he
          simp only [csat, List.any_cons, List.any_nil, Bool.or_false]
          rw [ln x hx, ln y (by omega), ln (x + y + z) (by omega)]
          simp only [Bool.or_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq]
          subst he
          omega
        · simp only [csat, List.any_cons, List.any_nil, Bool.or_false]
          rw [ln x hx, ln y (by omega), ln z (by omega), ln (x + y + z) (by omega)]
          simp only [Bool.or_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq]
          omega

/-- Encoding lemma: `Unsat (cnf N L)` for a list of valid tuples gives `¬ Colourable N 4`.
Every colouring is first renamed into the symmetry-broken form (`recol`, with `first_new`). -/
theorem not_colourable_of_unsat (N : Nat) (hN : 3 ≤ N) (L : List (Nat × Nat × Nat × Nat))
    (hL : L.all (validT N) = true) (hu : Unsat (cnf N L)) : ¬ Colourable N 4 := by
  rintro ⟨f, hf, hsf⟩
  have hab : f 1 ≠ f 3 := by
    intro he
    exact hsf 1 1 1 (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (by omega) ⟨rfl, rfl, he⟩
  obtain ⟨d, hd4, hda, hdb, hd⟩ := first_new f hf 1 N (f 1) (f 3)
  apply hu (val (recol f (f 1) (f 3) d))
  apply sat_of_broken N L hL _ (recol_lt f _ _ d)
  · intro x y z hx hxy hyz hw ⟨e1, e2, e3⟩
    have ri := fun u v (e : recol f (f 1) (f 3) d u = recol f (f 1) (f 3) d v) =>
      recol_inj f hf _ _ d u v (hf _) (hf _) hd4 hab hda hdb e
    exact hsf x y z hx hxy hyz hw ⟨ri _ _ e1, ri _ _ e2, ri _ _ e3⟩
  · unfold recol; simp
  · unfold recol; simp [Ne.symm hab]
  · intro i hi1 hi2 hgi
    obtain ⟨ea, eb, ed⟩ := recol_three f _ _ d i hgi
    obtain ⟨j, hj1, hj2, hj3⟩ := hd i (by omega) hi2 ea eb ed
    refine ⟨j, hj1, hj2, ?_⟩
    unfold recol
    rw [hj3]
    simp [hda, hdb]

/-- `chkF` over a concatenation splits into the two parts. -/
theorem chkF_append (S : T) : ∀ (A B : List (List Nat)) (j : Nat),
    chkF S (A ++ B) j = (chkF S A j && chkF S B (j + A.length))
  | [], B, j => by simp [chkF]
  | c :: cs, B, j => by
    rw [List.cons_append, chkF_cons, chkF_cons, chkF_append S cs B (j + 1), Bool.and_assoc]
    simp only [List.length_cons]
    rw [show j + 1 + cs.length = j + (cs.length + 1) by omega]

end E11Lrat
