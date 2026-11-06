import Mathlib

/-
OEIS A228469 and A228471 (Clark Kimberling, 2013).  Both are defined by
a(n) = 6 a(n-2) + a(n-4) (initial terms 2, 8, 13, 49 and 3, 5, 19, 31).
Conjectures: a(n) is the least positive c for which some positive b has trace(b, c)
equal to the first letters of 0101... (A228469) or 1010... (A228471).

Definitions.  `tr x y` is Kimberling's trace: while y does not divide x, with r = x mod y,
w = min(u, v), u = (y, r), v = (y, y - r); letter false (0) if w = u, i.e. r <= y - r,
true (1) otherwise.  `alt s n` is the alternating word of length n starting with s.
Reading: offset 0 with a(0) = 2 (resp. 3) for the one-letter word, so a(n) belongs to the
first n+1 letters (the empty trace is reached already for c = 1).

General result.  `A228469.least_c`: for every nonempty word w, the least c > 0 with
tr b c = w for some b > 0 is (W w).1, where W builds the pair (y_0, y_1) backward from the
last letter (start (2,1) or (3,1); a 0 maps (a,b) to (2a+b, a), a 1 to (3a-b, a)).
Lower bound `lower`: in coordinates t = y - 2 y_1, u = y_1 both backward maps are
monotone and the multipliers are at least 2 (letter 0) and 3 (letter 1).
Achievability `achieve`.

Main theorems.
* `A228469_conjecture n : IsLeast {c | 0 < c ∧ ∃ b, 0 < b ∧ tr b c = alt false (n+1)} (A228469 n)`
* `A228471_conjecture n : IsLeast {c | 0 < c ∧ ∃ b, 0 < b ∧ tr b c = alt true (n+1)} (A228471 n)`
via `A228469_W`, `A228471_W` (two backward steps act as (a,b) -> (5a+3b, 2a+b), resp.
(7a-2b, 3a-b), whose first coordinate satisfies x(n+4) = 6 x(n+2) + x(n)).
Not checked here: nothing beyond the reading of the definitions.
-/

namespace A228469

/-- Kimberling's trace of (x, y) (OEIS A228469): while y does not divide x, with r = x mod y,
apply w = min(u, v), u(x,y) = (y, r), v(x,y) = (y, y - r); record `false` (0) if w = u
(r ≤ y - r) and `true` (1) otherwise. -/
def tr (x y : ℕ) : List Bool :=
  if y = 0 then [] else
  if x % y = 0 then [] else
  if 2 * (x % y) ≤ y then false :: tr y (x % y) else true :: tr y (y - x % y)
termination_by y
decreasing_by
  · exact Nat.mod_lt _ (by omega)
  · omega

/-- The alternating word s, !s, s, ... of length n. -/
def alt (s : Bool) : ℕ → List Bool
  | 0 => []
  | n + 1 => s :: alt (!s) n

/-- Greedy minimal pair (y_0, y_1) for a nonempty word, built from the last letter backward. -/
def W : List Bool → ℕ × ℕ
  | [] => (0, 0)
  | [e] => (if e then 3 else 2, 1)
  | _ :: e' :: r => if e' then (3 * (W (e' :: r)).1 - (W (e' :: r)).2, (W (e' :: r)).1)
      else (2 * (W (e' :: r)).1 + (W (e' :: r)).2, (W (e' :: r)).1)

/-- The step after (x, y): the new second entry. -/
def nxt (x y : ℕ) : ℕ := if 2 * (x % y) ≤ y then x % y else y - x % y

lemma tr_cons {x y : ℕ} {e : Bool} {w : List Bool} (h : tr x y = e :: w) :
    0 < y ∧ x % y ≠ 0 ∧ (e = false ↔ 2 * (x % y) ≤ y) ∧ tr y (nxt x y) = w := by
  rw [tr] at h
  by_cases hy : y = 0
  · simp [hy] at h
  by_cases hr : x % y = 0
  · simp [hy, hr] at h
  refine ⟨Nat.pos_of_ne_zero hy, hr, ?_⟩
  by_cases h2 : 2 * (x % y) ≤ y
  · simp only [hy, hr, h2, ↓reduceIte, List.cons.injEq] at h
    exact ⟨by simp [← h.1, h2], by simpa [nxt, h2] using h.2⟩
  · simp only [hy, hr, h2, ↓reduceIte, List.cons.injEq] at h
    exact ⟨by simp [← h.1, h2], by simpa [nxt, h2] using h.2⟩

lemma tr_nil_of_dvd {x y : ℕ} (h : x % y = 0) : tr x y = [] := by
  rw [tr]; simp [h]

lemma W_inv : ∀ w : List Bool, w ≠ [] →
    1 ≤ (W w).2 ∧ 2 * (W w).2 ≤ (W w).1 ∧ (w.head? = some true → 2 * (W w).2 < (W w).1)
  | [] , h => absurd rfl h
  | [e], _ => by cases e <;> simp [W]
  | e :: e' :: r, _ => by
    have ih := W_inv (e' :: r) (by simp)
    cases e' <;> simp only [W, Bool.false_eq_true, ↓reduceIte] <;> refine ⟨by omega, by omega, ?_⟩ <;>
      intro _ <;> omega

/-- Lower bound: any (x, y) with trace w has y ≥ (W w).1. -/
lemma lower : ∀ w : List Bool, w ≠ [] → ∀ x y, tr x y = w →
    (W w).2 ≤ nxt x y ∧ (W w).1 - 2 * (W w).2 ≤ y - 2 * nxt x y ∧ 2 * nxt x y ≤ y
  | [], h, _, _, _ => absurd rfl h
  | [e], _, x, y, ht => by
    obtain ⟨hy, hr, he, -⟩ := tr_cons ht
    have hlt : x % y < y := Nat.mod_lt _ hy
    unfold nxt
    cases e
    · have h2 : 2 * (x % y) ≤ y := he.mp rfl
      simp only [W, Bool.false_eq_true, ↓reduceIte, h2]
      refine ⟨?_, ?_, ?_⟩ <;> first | trivial | omega
    · have h2 : ¬ 2 * (x % y) ≤ y := fun h => absurd (he.mpr h) (by simp)
      simp only [W, ↓reduceIte, h2]
      refine ⟨?_, ?_, ?_⟩ <;> omega
  | e :: e' :: r, _, x, y, ht => by
    obtain ⟨hy, hr, he, ht'⟩ := tr_cons ht
    have hlt : x % y < y := Nat.mod_lt _ hy
    have ih := lower (e' :: r) (by simp) y (nxt x y) ht'
    obtain ⟨hy1, hr1, he1, -⟩ := tr_cons ht'
    have hinv := W_inv (e' :: r) (by simp)
    set y1 := nxt x y with hy1def
    have h2 : 2 * y1 ≤ y := by rw [hy1def]; unfold nxt; split_ifs <;> omega
    -- y mod y1 ≤ y - 2 y1, since y / y1 ≥ 2
    have hq : 2 ≤ y / y1 := (Nat.le_div_iff_mul_le hy1).mpr (by omega)
    have hdm := Nat.div_add_mod y y1
    have hm : y % y1 ≤ y - 2 * y1 := by
      have := Nat.mul_le_mul_left y1 hq
      omega
    have hlt1 : y % y1 < y1 := Nat.mod_lt _ hy1
    refine ⟨?_, ?_, h2⟩
    · cases e' <;> simp only [W, Bool.false_eq_true, ↓reduceIte] <;> omega
    · revert ih; unfold nxt at *
      cases e' <;> simp at he1 <;> simp only [W, Bool.false_eq_true, ↓reduceIte] <;>
        split_ifs <;> intro ih <;> omega

lemma lower_c (w : List Bool) (hw : w ≠ []) (x y : ℕ) (ht : tr x y = w) : (W w).1 ≤ y := by
  have := lower w hw x y ht
  have := W_inv w hw
  omega

/-- One trace step from a pair built greedily. -/
lemma tr_step_false {a b : ℕ} (hb : 1 ≤ b) (hab : 2 * b ≤ a) : tr (2 * a + b) a = false :: tr a b := by
  have hm : (2 * a + b) % a = b := by
    rw [show 2 * a + b = b + a * 2 by ring, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
  rw [tr]; simp [hm, show a ≠ 0 by omega, show b ≠ 0 by omega, hab]

lemma tr_step_true {a b : ℕ} (hb : 1 ≤ b) (hab : 2 * b < a) : tr (3 * a - b) a = true :: tr a b := by
  have hm : (3 * a - b) % a = a - b := by
    rw [show 3 * a - b = (a - b) + a * 2 by omega, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
  rw [tr]
  simp [hm, show a ≠ 0 by omega, show a - b ≠ 0 by omega, show ¬ (2 * (a - b) ≤ a) by omega,
    show a - (a - b) = b by omega]

lemma achieve_tail : ∀ w : List Bool, w ≠ [] → tr (W w).1 (W w).2 = w.tail
  | [], h => absurd rfl h
  | [e], _ => by cases e <;> simp [W] <;> exact tr_nil_of_dvd (by norm_num)
  | e :: e' :: r, _ => by
    have ih := achieve_tail (e' :: r) (by simp)
    have hinv := W_inv (e' :: r) (by simp)
    simp only [List.tail_cons] at ih ⊢
    cases e'
    · simp only [W, Bool.false_eq_true, ↓reduceIte]
      rw [tr_step_false hinv.1 hinv.2.1, ih]
    · simp only [W, ↓reduceIte]
      rw [tr_step_true hinv.1 (hinv.2.2 rfl), ih]

lemma achieve (w : List Bool) (hw : w ≠ []) : ∃ b, 0 < b ∧ tr b (W w).1 = w := by
  have ih := achieve_tail w hw
  have hinv := W_inv w hw
  obtain ⟨e, w', rfl⟩ : ∃ e w', w = e :: w' := by
    cases w with
    | nil => exact absurd rfl hw
    | cons e w' => exact ⟨e, w', rfl⟩
  cases e
  · refine ⟨2 * (W (false :: w')).1 + (W (false :: w')).2, by omega, ?_⟩
    rw [tr_step_false hinv.1 hinv.2.1, ih]; rfl
  · refine ⟨3 * (W (true :: w')).1 - (W (true :: w')).2, by have := hinv.2.2 rfl; omega, ?_⟩
    rw [tr_step_true hinv.1 (hinv.2.2 rfl), ih]; rfl

/-- The least c with some b > 0 and trace(b, c) = w is (W w).1. -/
theorem least_c (w : List Bool) (hw : w ≠ []) :
    IsLeast {c | 0 < c ∧ ∃ b, 0 < b ∧ tr b c = w} (W w).1 := by
  refine ⟨⟨by have := W_inv w hw; omega, achieve w hw⟩, ?_⟩
  rintro c ⟨-, b, -, hb⟩
  exact lower_c w hw b c hb

lemma W_alt (s : Bool) (n : ℕ) : W (alt s (n+2)) =
    if (!s) then (3 * (W (alt (!s) (n+1))).1 - (W (alt (!s) (n+1))).2, (W (alt (!s) (n+1))).1)
    else (2 * (W (alt (!s) (n+1))).1 + (W (alt (!s) (n+1))).2, (W (alt (!s) (n+1))).1) := by
  simp only [alt, W]

lemma alt_ne (s : Bool) (n : ℕ) : alt s (n+1) ≠ [] := by simp [alt]

lemma W_two_false (n : ℕ) :
    (W (alt false (n+3))).1 = 5 * (W (alt false (n+1))).1 + 3 * (W (alt false (n+1))).2 ∧
    (W (alt false (n+3))).2 = 2 * (W (alt false (n+1))).1 + (W (alt false (n+1))).2 := by
  rw [W_alt false (n+1)]
  simp only [Bool.not_false, ↓reduceIte]
  rw [W_alt true n]
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  exact ⟨by omega, trivial⟩

lemma W_two_true (n : ℕ) :
    (W (alt true (n+3))).1 + 2 * (W (alt true (n+1))).2 = 7 * (W (alt true (n+1))).1 ∧
    (W (alt true (n+3))).2 + (W (alt true (n+1))).2 = 3 * (W (alt true (n+1))).1 := by
  have hinv := W_inv (alt true (n+1)) (alt_ne _ _)
  rw [W_alt true (n+1)]
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  rw [W_alt false n]
  simp only [Bool.not_false, ↓reduceIte]
  omega

end A228469

/-- OEIS A228469: a(n) = 6 a(n-2) + a(n-4), a(0..3) = 2, 8, 13, 49. -/
def A228469 : ℕ → ℕ
  | 0 => 2 | 1 => 8 | 2 => 13 | 3 => 49
  | n + 4 => 6 * A228469 (n + 2) + A228469 n

/-- OEIS A228471: a(n) = 6 a(n-2) + a(n-4), a(0..3) = 3, 5, 19, 31. -/
def A228471 : ℕ → ℕ
  | 0 => 3 | 1 => 5 | 2 => 19 | 3 => 31
  | n + 4 => 6 * A228471 (n + 2) + A228471 n

open A228469 in
theorem A228469_W (n : ℕ) : (W (alt false (n+1))).1 = A228469 n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih with
    | 0, _ => decide
    | 1, _ => decide
    | 2, _ => decide
    | 3, _ => decide
    | m + 4, ih =>
      have h1 := ih m (by omega)
      have h2 := ih (m + 2) (by omega)
      have e1 := W_two_false m
      have e2 := W_two_false (m + 2)
      simp only [A228469]
      rw [show m + 2 + 1 = m + 3 by omega] at h2 e2
      rw [show m + 4 + 1 = m + 2 + 3 by omega]
      omega

open A228469 in
theorem A228471_W (n : ℕ) : (W (alt true (n+1))).1 = A228471 n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih with
    | 0, _ => decide
    | 1, _ => decide
    | 2, _ => decide
    | 3, _ => decide
    | m + 4, ih =>
      have h1 := ih m (by omega)
      have h2 := ih (m + 2) (by omega)
      have e1 := W_two_true m
      have e2 := W_two_true (m + 2)
      simp only [A228471]
      rw [show m + 2 + 1 = m + 3 by omega] at h2 e2
      rw [show m + 4 + 1 = m + 2 + 3 by omega]
      omega

open A228469 in
/-- Kimberling's conjecture in A228469: a(n) is the least c > 0 for which some b > 0 has
trace(b, c) equal to the first n+1 letters of 0101... (offset 0: a(0) = 2 for the word 0). -/
theorem A228469_conjecture (n : ℕ) :
    IsLeast {c | 0 < c ∧ ∃ b, 0 < b ∧ tr b c = alt false (n+1)} (A228469 n) := by
  rw [← A228469_W]; exact least_c _ (alt_ne _ _)

open A228469 in
/-- Kimberling's conjecture in A228471: the same with the word 1010... -/
theorem A228471_conjecture (n : ℕ) :
    IsLeast {c | 0 < c ∧ ∃ b, 0 < b ∧ tr b c = alt true (n+1)} (A228471 n) := by
  rw [← A228471_W]; exact least_c _ (alt_ne _ _)

open A228469
