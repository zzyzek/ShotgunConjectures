import Mathlib

/-!
# OEIS A221564: a(3k+1) = 2k for the FO4C3 shuffle

Positions `0, ..., n-1` from the top; a card is `(position, flipped)`. One FO4C3 move (flip the
top four as a unit, then cut three cards from top to bottom) sends a card at position `p` to
`mv n (p, b)`: positions `1, 2, 3` go to `n-1, n-2, n-3` and are flipped, position `0` stays on top
and is flipped, positions `p ≥ 4` go to `p - 3`.

Checked (Lean with Mathlib for `Function.iterate`, all `k ≥ 1`, `n = 3k+1`): `restored_2k` (after `2k` moves every card is back in
place with its original orientation) and `not_restored` (for `0 < j < 2k` the card starting at
position 2 is not back unflipped). Hence the least number of moves is `2k`.
Not checked: the translation of the card move into `mv` (checked against a deck simulation and the
data, n = 4..30, `certificate/simulate.py`).
-/

namespace A221564

def mv (n : Nat) (s : Nat × Bool) : Nat × Bool :=
  if s.1 = 0 then (0, !s.2) else if s.1 ≤ 3 then (n - s.1, !s.2) else (s.1 - 3, s.2)

def restored (n j : Nat) : Prop := ∀ p, p < n → (mv n)^[j] (p, false) = (p, false)

theorem mv_top (n : Nat) (b : Bool) : mv n (0, b) = (0, !b) := by simp [mv]

theorem mv_small (n p : Nat) (b : Bool) (h1 : 1 ≤ p) (h3 : p ≤ 3) : mv n (p, b) = (n - p, !b) := by
  simp only [mv]; split_ifs <;> first | rfl | (exfalso; omega)

theorem mv_big (n p : Nat) (b : Bool) (h4 : 4 ≤ p) : mv n (p, b) = (p - 3, b) := by
  simp only [mv]; split_ifs <;> first | rfl | (exfalso; omega)

theorem down (n : Nat) : ∀ t p b, 3 * t + 1 ≤ p → (mv n)^[t] (p, b) = (p - 3 * t, b) := by
  intro t
  induction t with
  | zero => intro p b _; simp
  | succ t ih =>
    intro p b h
    rw [Function.iterate_succ_apply', ih p b (by omega), mv_big _ _ _ (by omega)]
    rw [show p - 3 * t - 3 = p - 3 * (t + 1) by omega]

theorem iter_add (n a c : Nat) (s : Nat × Bool) : (mv n)^[a + c] s = (mv n)^[c] ((mv n)^[a] s) := by
  rw [Nat.add_comm, Function.iterate_add_apply]


theorem top_iter (n j : Nat) (b : Bool) : (mv n)^[j] (0, b) = (0, if j % 2 = 0 then b else !b) := by
  induction j generalizing b with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply, mv_top, ih]
    rcases Nat.mod_two_eq_zero_or_one j with h | h
    · have h' : (j + 1) % 2 = 1 := by omega
      simp [h, h']
    · have h' : (j + 1) % 2 = 0 := by omega
      simp [h, h']

theorem dn (N t p q : Nat) (b : Bool) (h : 3 * t + 1 ≤ p) (hq : p - 3 * t = q) :
    (mv N)^[t] (p, b) = (q, b) := by
  rw [down N t p b h, hq]

theorem sm (N p q : Nat) (b : Bool) (h1 : 1 ≤ p) (h3 : p ≤ 3) (hq : N - p = q) :
    (mv N)^[1] (p, b) = (q, !b) := by
  rw [Function.iterate_one, mv_small N p b h1 h3, hq]

/-- residue 2: `3r + 2 → ... → 2 → 3k - 1 (flip) → ... → 3r + 2`, `k` moves, one flip. -/
theorem cyc2 (k r : Nat) (b : Bool) (hr : r + 1 ≤ k) :
    (mv (3 * k + 1))^[k] (3 * r + 2, b) = (3 * r + 2, !b) := by
  have e : k = r + (1 + (k - 1 - r)) := by omega
  rw [e, iter_add, dn _ r _ 2 b (by omega) (by omega), iter_add,
    sm _ 2 (3 * k - 1) b (by omega) (by omega) (by omega),
    dn _ _ _ (3 * r + 2) _ (by omega) (by omega)]

/-- residue 0: `3r → ... → 3 → 3k-2 (flip) → ... → 1 → 3k (flip) → ... → 3r`. -/
theorem cyc0 (k r : Nat) (b : Bool) (h1 : 1 ≤ r) (hr : r ≤ k) :
    (mv (3 * k + 1))^[2 * k] (3 * r, b) = (3 * r, b) := by
  have e : 2 * k = (r - 1) + (1 + ((k - 1) + (1 + (k - r)))) := by omega
  rw [e, iter_add, dn _ (r - 1) _ 3 b (by omega) (by omega), iter_add,
    sm _ 3 (3 * k - 2) b (by omega) (by omega) (by omega), iter_add,
    dn _ (k - 1) _ 1 _ (by omega) (by omega), iter_add,
    sm _ 1 (3 * k) _ (by omega) (by omega) (by omega), Bool.not_not,
    dn _ _ _ (3 * r) _ (by omega) (by omega)]

/-- residue 1: `3r+1 → ... → 1 → 3k (flip) → ... → 3 → 3k-2 (flip) → ... → 3r+1`. -/
theorem cyc1 (k r : Nat) (b : Bool) (hr : r + 1 ≤ k) :
    (mv (3 * k + 1))^[2 * k] (3 * r + 1, b) = (3 * r + 1, b) := by
  have e : 2 * k = r + (1 + ((k - 1) + (1 + (k - 1 - r)))) := by omega
  rw [e, iter_add, dn _ r _ 1 b (by omega) (by omega), iter_add,
    sm _ 1 (3 * k) b (by omega) (by omega) (by omega), iter_add,
    dn _ (k - 1) _ 3 _ (by omega) (by omega), iter_add,
    sm _ 3 (3 * k - 2) _ (by omega) (by omega) (by omega), Bool.not_not,
    dn _ _ _ (3 * r + 1) _ (by omega) (by omega)]

theorem restored_2k (k : Nat) : restored (3 * k + 1) (2 * k) := by
  intro p hp
  rcases (by omega : p = 0 ∨ p % 3 = 0 ∧ 1 ≤ p ∨ p % 3 = 1 ∨ p % 3 = 2) with h | h | h | h
  · subst h; rw [top_iter]; simp
  · have := cyc0 k (p / 3) false (by omega) (by omega)
    rwa [show 3 * (p / 3) = p by omega] at this
  · have := cyc1 k (p / 3) false (by omega)
    rwa [show 3 * (p / 3) + 1 = p by omega] at this
  · have h2 := cyc2 k (p / 3) false (by omega)
    rw [show 3 * (p / 3) + 2 = p by omega] at h2
    rw [show 2 * k = k + k by omega, iter_add, h2]
    have h3 := cyc2 k (p / 3) true (by omega)
    rw [show 3 * (p / 3) + 2 = p by omega] at h3
    simp only [Bool.not_false, Bool.not_true] at h3 ⊢
    rw [h3]

/-- The orbit of the card at position 2 for `1 ≤ j ≤ k`. -/
theorem orbit2 (k j : Nat) (b : Bool) (h1 : 1 ≤ j) (hj : j ≤ k) :
    (mv (3 * k + 1))^[j] (2, b) = (3 * k + 2 - 3 * j, !b) := by
  have e : j = 1 + (j - 1) := by omega
  rw [e, iter_add, sm _ 2 (3 * k - 1) b (by omega) (by omega) (by omega),
    dn _ _ _ (3 * k + 2 - 3 * (1 + (j - 1))) _ (by omega) (by omega)]

theorem not_restored (k j : Nat) (hk : 1 ≤ k) (hj0 : 0 < j) (hj : j < 2 * k) :
    ¬ restored (3 * k + 1) j := by
  intro h
  have h2 := h 2 (by omega)
  rcases Nat.lt_or_ge k j with hkj | hkj
  · have e : j = k + (j - k) := by omega
    rw [e, iter_add, orbit2 k k false hk le_rfl, show 3 * k + 2 - 3 * k = 2 by omega,
      Bool.not_false, orbit2 k (j - k) true (by omega) (by omega)] at h2
    have := congrArg Prod.fst h2; simp only at this; omega
  · rw [orbit2 k j false hj0 hkj] at h2
    have := congrArg Prod.snd h2; simp at this

/-- A221564(3k+1) = 2k: `2k` moves restore the packet and no smaller positive number does. -/
theorem A221564_main (k : Nat) (hk : 1 ≤ k) :
    restored (3 * k + 1) (2 * k) ∧ ∀ j, 0 < j → j < 2 * k → ¬ restored (3 * k + 1) j :=
  ⟨restored_2k k, fun j h0 h1 => not_restored k j hk h0 h1⟩
