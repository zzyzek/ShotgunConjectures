import Mathlib

/-!
# OEIS A214444 vs A214451: the block boundaries never coincide

A214444: blocks of consecutive squares starting at 0^2, each block the shortest one (length a(n)) whose
arithmetic mean is prime. A214451: the same starting at 1^2. Conjecture (A214444): for some k and x,
a(n) = A214451(n + x) for n > k.

Checked here: for every block s^2, ..., (s+L-1)^2 (L >= 1) with prime mean, s mod 4 ∈ {0, 3} iff
(s + L) mod 4 ∈ {0, 3} (`block_class`). Hence every block start of A214444 is ≡ 0, 3 (mod 4) and every
block start of A214451 is ≡ 1, 2 (mod 4), so the two block partitions never share a boundary
(`A214444_A214451_starts_disjoint`). This does not settle the conjecture: it only shows that eventual agreement
of the lengths would need the two partitions to be translates by an offset D ≡ 2 (mod 4).
Not checked: nothing beyond reading the definitions (`nextLen`, `startA`, `startB`).
-/

open Classical

/-- s^2 + (s+1)^2 + ... + (s+L-1)^2. -/
def sqSum (s : ℕ) : ℕ → ℕ
  | 0 => 0
  | L + 1 => sqSum s L + (s + L) ^ 2

/-- The block of length L at s has prime mean. -/
def goodBlock (s L : ℕ) : Prop := 1 ≤ L ∧ ∃ M, M.Prime ∧ L * M = sqSum s L

/-- Least L with prime mean (0 if none; then the sequence would stop). -/
noncomputable def nextLen (s : ℕ) : ℕ := if h : ∃ L, goodBlock s L then Nat.find h else 0

/-- Block starts of A214444 (from 0) and A214451 (from 1); a(n) = nextLen (start (n-1)). -/
noncomputable def startA : ℕ → ℕ
  | 0 => 0
  | i + 1 => startA i + nextLen (startA i)

noncomputable def startB : ℕ → ℕ
  | 0 => 1
  | i + 1 => startB i + nextLen (startB i)

theorem six_sqSum (s l : ℕ) :
    6 * sqSum s (l + 1) = (l + 1) * (6 * s ^ 2 + 6 * s * l + l * (2 * l + 1)) := by
  induction l with
  | zero => simp [sqSum]
  | succ l ih =>
    rw [sqSum, mul_add, ih]
    ring

def cls (s : ℕ) : Prop := (s : ZMod 4) = 0 ∨ (s : ZMod 4) = 3

theorem residue_table : ∀ a b m : ZMod 4, (m = 1 ∨ m = 3) →
    6 * m = 6 * a ^ 2 + 6 * a * b + b * (2 * b + 1) →
    ((a = 0 ∨ a = 3) ↔ (a + (b + 1) = 0 ∨ a + (b + 1) = 3)) := by
  decide

theorem block_class (s L : ℕ) (h : goodBlock s L) : (cls s ↔ cls (s + L)) := by
  obtain ⟨hL, M, hM, hsum⟩ := h
  obtain ⟨l, rfl⟩ : ∃ l, L = l + 1 := ⟨L - 1, by omega⟩
  have hE : 6 * M = 6 * s ^ 2 + 6 * s * l + l * (2 * l + 1) := by
    have h6 := six_sqSum s l
    rw [← hsum] at h6
    have : (l + 1) * (6 * M) = (l + 1) * (6 * s ^ 2 + 6 * s * l + l * (2 * l + 1)) := by
      rw [← h6]; ring
    exact Nat.eq_of_mul_eq_mul_left (by omega) this
  have hM2 : M ≠ 2 := by
    rintro rfl
    have hl : l ≤ 2 := by nlinarith
    have hs : s ≤ 1 := by nlinarith
    interval_cases l <;> interval_cases s <;> omega
  have hodd : M % 4 = 1 ∨ M % 4 = 3 := by
    have := hM.eq_one_or_self_of_dvd 2
    rcases Nat.even_or_odd M with ⟨c, hc⟩ | ⟨c, hc⟩
    · exact absurd (this ⟨c, by omega⟩) (by omega)
    · omega
  have hm : ((M : ZMod 4) = 1 ∨ (M : ZMod 4) = 3) := by
    rw [← ZMod.natCast_mod M 4]
    rcases hodd with h | h <;> rw [h] <;> simp
  have hcast : (6 : ZMod 4) * M = 6 * (s : ZMod 4) ^ 2 + 6 * s * l + l * (2 * l + 1) := by
    exact_mod_cast congrArg (fun n : ℕ => (n : ZMod 4)) hE
  have := residue_table s l M hm hcast
  unfold cls
  push_cast
  exact this

theorem cls_step (s : ℕ) : (cls s ↔ cls (s + nextLen s)) := by
  unfold nextLen
  split_ifs with h
  · exact block_class s _ (Nat.find_spec h)
  · simp

theorem startA_cls (i : ℕ) : cls (startA i) := by
  induction i with
  | zero => left; simp [startA]
  | succ i ih => exact (cls_step _).mp ih

theorem startB_not_cls (i : ℕ) : ¬ cls (startB i) := by
  induction i with
  | zero => simp only [startB, cls, Nat.cast_one]; decide
  | succ i ih => exact fun h => ih ((cls_step _).mpr h)

/-- Main theorem: no block boundary of A214444 is a block boundary of A214451. -/
theorem A214444_A214451_starts_disjoint (i j : ℕ) : startA i ≠ startB j := by
  intro h
  exact startB_not_cls j (h ▸ startA_cls i)
