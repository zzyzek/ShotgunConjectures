/-
Guy, UPINT E13 (Turán): s(m, n) is the least s such that every partition of [m, m + s] into
n classes has a class containing x + y = z (x = y allowed). Known: s(m, 2) = 4m.

Checked here (`colouring3_sumfree`): for every m ≥ 1 the explicit 3-colouring `col3 m` of
[m, 14m - 1] has no monochromatic x + y = z, so s(m, 3) ≥ 13m (the Abbott-Znám doubling step
applied to Turán's 2-colouring). Also `colouring2_sumfree` (s(m, 2) ≥ 4m).
Checked here (`schur3`): every 3-colouring of [1, 14] has a monochromatic x + y = z (Schur
number S(3) = 13), by a backtracking search `search` evaluated by the kernel (`decide`) and a
soundness proof (`sound`). Scaling by m (`upper3`): {m, 2m, ..., 14m} ⊆ [m, 14m].
Main theorem `s_m_3`: with `Colourable m s n` = "[m, m + s] has an n-colouring with no
monochromatic x + y = z", Colourable m (13m - 1) 3 holds and Colourable m (13m) 3 fails,
i.e. s(m, 3) = 13m, for every m ≥ 1.
Not checked here: the values of s(m, 4) (SAT computation, see README).
-/

namespace NT_E13_1

/-- Colour of x under the list l (l[i] is the colour of i + 1). -/
def col (l : List Nat) (x : Nat) : Nat := l.getD (x - 1) 0

/-- Adding colour c as the colour of k = l.length + 1 creates a monochromatic a + (k - a) = k. -/
def newBad (l : List Nat) (c : Nat) : Bool :=
  (List.range (l.length + 1)).any (fun a =>
    decide (1 ≤ a) && decide (2 * a ≤ l.length + 1) && decide (col l a = c) &&
      decide (col l (l.length + 1 - a) = c))

/-- true iff every extension of l by k more colours (each < 3) creates a monochromatic triple. -/
def search : Nat → List Nat → Bool
  | 0, _ => false
  | k + 1, l => [0, 1, 2].all (fun c => newBad l c || search k (l ++ [c]))

theorem search14 : search 14 [] = true := by decide

theorem col_append_lt (l : List Nat) (c x : Nat) (h1 : 1 ≤ x) (h2 : x ≤ l.length) :
    col (l ++ [c]) x = col l x := by
  unfold col
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_left (by omega)]

theorem col_append_last (l : List Nat) (c : Nat) : col (l ++ [c]) (l.length + 1) = c := by
  unfold col
  simp

theorem sound : ∀ (k : Nat) (l : List Nat) (f : Nat → Nat), (∀ x, f x < 3) →
    (∀ x, 1 ≤ x → x ≤ l.length → col l x = f x) → search k l = true →
    ∃ a b, 1 ≤ a ∧ a ≤ b ∧ a + b ≤ l.length + k ∧ f a = f b ∧ f b = f (a + b)
  | 0, _, _, _, _, h => by simp [search] at h
  | k + 1, l, f, hf, hl, h => by
    have hc : f (l.length + 1) = 0 ∨ f (l.length + 1) = 1 ∨ f (l.length + 1) = 2 := by
      have := hf (l.length + 1); omega
    have step : newBad l (f (l.length + 1)) = true ∨ search k (l ++ [f (l.length + 1)]) = true := by
      simp only [search, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
        Bool.or_eq_true] at h
      rcases hc with hc | hc | hc <;> rw [hc] <;> simp_all
    rcases step with hb | hs
    · simp only [newBad, List.any_eq_true, List.mem_range, Bool.and_eq_true,
        decide_eq_true_eq] at hb
      obtain ⟨a, _, ⟨⟨⟨ha1, ha2⟩, hca⟩, hcb⟩⟩ := hb
      refine ⟨a, l.length + 1 - a, ha1, by omega, by omega, ?_, ?_⟩
      · rw [← hl a ha1 (by omega), ← hl (l.length + 1 - a) (by omega) (by omega), hca, hcb]
      · rw [← hl (l.length + 1 - a) (by omega) (by omega), hcb,
          show a + (l.length + 1 - a) = l.length + 1 by omega]
    · have hl' : ∀ x, 1 ≤ x → x ≤ (l ++ [f (l.length + 1)]).length →
          col (l ++ [f (l.length + 1)]) x = f x := by
        intro x h1 h2
        simp only [List.length_append, List.length_cons, List.length_nil] at h2
        rcases Nat.lt_or_ge x (l.length + 1) with hx | hx
        · rw [col_append_lt l _ x h1 (by omega)]; exact hl x h1 (by omega)
        · have : x = l.length + 1 := by omega
          subst this; exact col_append_last l _
      obtain ⟨a, b, h1, h2, h3, h4, h5⟩ := sound k _ f hf hl' hs
      refine ⟨a, b, h1, h2, ?_, h4, h5⟩
      simp only [List.length_append, List.length_cons, List.length_nil] at h3
      omega

/-- Schur: every colouring of [1, 14] with 3 colours has a monochromatic x + y = z. -/
theorem schur3 (f : Nat → Nat) (hf : ∀ x, f x < 3) :
    ∃ a b, 1 ≤ a ∧ a ≤ b ∧ a + b ≤ 14 ∧ f a = f b ∧ f b = f (a + b) := by
  have := sound 14 [] f hf (fun x h1 h2 => by simp at h2; omega) search14
  simpa using this

/-- Turán's sum-free 2-colouring of [m, 5m - 1]: class 0 = [m, 2m) ∪ [4m, 5m), class 1 = [2m, 4m). -/
def col2 (m x : Nat) : Nat := if x < 2 * m then 0 else if x < 4 * m then 1 else 0

/-- 3-colouring of [m, 14m - 1]: col2 on [m, 5m), class 2 on [5m, 10m), col2 shifted by 9m on
[10m, 14m). -/
def col3 (m x : Nat) : Nat :=
  if x < 5 * m then col2 m x else if x < 10 * m then 2 else col2 m (x - 9 * m)

theorem colouring2_sumfree (m x y : Nat) (hx : m ≤ x) (hxy : x ≤ y) (hz : x + y < 5 * m) :
    ¬ (col2 m x = col2 m y ∧ col2 m y = col2 m (x + y)) := by
  unfold col2; intro h; (repeat' split at h) <;> omega

theorem colouring3_sumfree (m x y : Nat) (hx : m ≤ x) (hxy : x ≤ y) (hz : x + y < 14 * m) :
    ¬ (col3 m x = col3 m y ∧ col3 m y = col3 m (x + y)) := by
  unfold col3 col2; intro h; (repeat' split at h) <;> omega

/-- [m, m + s] has an n-colouring (colours < n) with no monochromatic x + y = z. -/
def Colourable (m s n : Nat) : Prop :=
  ∃ f : Nat → Nat, (∀ x, f x < n) ∧
    ∀ x y, m ≤ x → x ≤ y → x + y ≤ m + s → ¬ (f x = f y ∧ f y = f (x + y))

theorem upper3 (m : Nat) : ¬ Colourable m (13 * m) 3 := by
  rintro ⟨f, hf, hsf⟩
  obtain ⟨a, b, h1, h2, h3, h4, h5⟩ := schur3 (fun i => f (m * i)) (fun x => hf _)
  apply hsf (m * a) (m * b) (Nat.le_mul_of_pos_right m h1) (Nat.mul_le_mul_left m h2)
  · have : m * a + m * b = m * (a + b) := (Nat.mul_add m a b).symm
    have h14 : m * (a + b) ≤ m * 14 := Nat.mul_le_mul_left m h3
    omega
  · refine ⟨h4, ?_⟩
    rw [h5, Nat.mul_add]

theorem lower3 (m : Nat) (hm : 1 ≤ m) : Colourable m (13 * m - 1) 3 := by
  refine ⟨col3 m, fun x => ?_, fun x y hx hxy hz => colouring3_sumfree m x y hx hxy (by omega)⟩
  unfold col3 col2; (repeat' split) <;> omega

/-- Turán's s(m, n) for n = 3: s(m, 3) = 13m for every m ≥ 1. -/
theorem s_m_3 (m : Nat) (hm : 1 ≤ m) :
    Colourable m (13 * m - 1) 3 ∧ ¬ Colourable m (13 * m) 3 :=
  ⟨lower3 m hm, upper3 m⟩
