/-
OEIS A227145: a(n) = n - 1 - a(n-1) - a(a(n-2)) - a(a(a(n-3))) - ...,
with a(n) = 0 for n <= 1 (Frank Ruskey, 2013).
Conjecture (entry text): a(F_n) = F_(n-2) for n > 1 (F = Fibonacci numbers).
Celaya and Ruskey (arXiv:1307.0153, Prop. 10) proved the even case
a(F_(2n)) = F_(2n-2) and left the odd case open.

Definitions.
* The recurrence is taken as stated in the entry's FORMULA line and Mathematica
  program: for integers n >= 2, a n = n - 1 - Σ_{i=1..n} a^[i] (n - i), and
  a n = 0 for n <= 1 (terms with i >= n vanish).
* `blk k = [k+1, 0, ..., 0]` (k+1 zeros), `sig l = l.flatMap blk`,
  `Wl 0 = []`, `Wl (k+1) = 0 :: sig (Wl k)`; the lists Wl k are prefixes of one
  infinite word w (0-indexed, `w i`), with w = 0 · sig(w).
* `c n` = number of nonzero letters among w 0, ..., w (n-1).

Main theorems.
* `C_rec`: n ↦ c n (extended by 0 to negative integers) satisfies the
  recurrence.
* `eq_C`: every solution a : ℤ → ℤ of the recurrence equals it.
* `A227145_conjecture`: every solution a satisfies a (fib m) = fib (m - 2)
  for all m >= 2.

Route. Block structure of w: with st p = 1 + 2p + Σ_{q<p} w q, the letters
w (st p) .. w (st p + w p + 1) are w p + 1, 0, ..., 0 (`w_st`, `w_st_add`), and
these blocks tile the positions >= 1 (`cover`, `block_unique`).
`c_iter_step`: c^[j] (u+1) - c^[j] u = [j <= w u]. `coverage`: for t >= 1,
#{j in 1..t : j <= w (t - j)} = [w t = 0]. Together they give the
recurrence (`rec_nat`). Fibonacci values from st (fib (2k+1)) = fib (2k+3) + 1
and st (fib (2k+2)) = fib (2k+4) (`fib_odd`, `fib_even`).

Not checked in this file: agreement with the OEIS data terms
(certificate/check_A227145.py).
-/
import Mathlib

open Finset

namespace A227145

/-! ### The word -/

def blk (k : ℕ) : List ℕ := (k + 1) :: List.replicate (k + 1) 0

def sig (l : List ℕ) : List ℕ := l.flatMap blk

def Wl : ℕ → List ℕ
  | 0 => []
  | k + 1 => 0 :: sig (Wl k)

theorem sig_append (l m : List ℕ) : sig (l ++ m) = sig l ++ sig m := by
  simp [sig, List.flatMap_append]

theorem sig_length (l : List ℕ) : (sig l).length = 2 * l.length + l.sum := by
  induction l with
  | nil => simp [sig]
  | cons x l ih =>
    rw [show x :: l = [x] ++ l from rfl, sig_append, List.length_append, ih]
    simp [sig, blk]; ring

theorem sig_prefix {l m : List ℕ} (h : l <+: m) : sig l <+: sig m := by
  obtain ⟨u, rfl⟩ := h
  rw [sig_append]; exact List.prefix_append _ _

theorem Wl_prefix_succ (k : ℕ) : Wl k <+: Wl (k + 1) := by
  induction k with
  | zero => simp [Wl]
  | succ k ih =>
    show 0 :: sig (Wl k) <+: 0 :: sig (Wl (k + 1))
    exact (List.prefix_cons_inj 0).mpr (sig_prefix ih)

theorem Wl_prefix {k k' : ℕ} (h : k ≤ k') : Wl k <+: Wl k' := by
  induction h with
  | refl => exact List.prefix_refl _
  | step _ ih => exact ih.trans (Wl_prefix_succ _)

theorem Wl_length (k : ℕ) : k ≤ (Wl k).length := by
  induction k with
  | zero => simp
  | succ k ih =>
    show k + 1 ≤ (0 :: sig (Wl k)).length
    rw [List.length_cons, sig_length]; omega

/-- The infinite word, 0-indexed. -/
def w (i : ℕ) : ℕ := (Wl (i + 1)).getD i 0

theorem w_of_get {k i x : ℕ} (h : (Wl k)[i]? = some x) : w i = x := by
  have hi : i < (Wl k).length := by
    by_contra hc; rw [List.getElem?_eq_none (by omega)] at h; exact absurd h (by simp)
  have hi' : i < (Wl (i + 1)).length := lt_of_lt_of_le (Nat.lt_succ_self i) (Wl_length _)
  unfold w
  rw [List.getD_eq_getElem?_getD]
  have : (Wl (i + 1))[i]? = some x := by
    rcases le_total k (i + 1) with hk | hk
    · obtain ⟨u, hu⟩ := Wl_prefix hk; rw [← hu, List.getElem?_append_left hi, h]
    · obtain ⟨u, hu⟩ := Wl_prefix hk; rw [← hu, List.getElem?_append_left hi'] at h; exact h
  rw [this]; rfl

theorem w_eq {k i : ℕ} (h : i < (Wl k).length) : (Wl k)[i] = w i :=
  (w_of_get (List.getElem?_eq_getElem h)).symm

theorem w_zero : w 0 = 0 := w_of_get (k := 1) rfl

/-- Λ p = w 0 + ... + w (p-1). -/
def Λ (p : ℕ) : ℕ := ∑ q ∈ range p, w q

def st (p : ℕ) : ℕ := 1 + 2 * p + Λ p

theorem st_succ (p : ℕ) : st (p + 1) = st p + w p + 2 := by
  simp [st, Λ, sum_range_succ]; ring

theorem take_sum (l : List ℕ) (p : ℕ) (hp : p ≤ l.length) (hl : ∀ i (h : i < l.length), l[i] = w i) :
    (l.take p).sum = Λ p := by
  induction p with
  | zero => simp [Λ]
  | succ p ih =>
    rw [List.take_add_one, List.sum_append, ih (by omega), List.getElem?_eq_getElem (by omega)]
    simp [Λ, sum_range_succ, hl p (by omega)]

theorem sig_get (l : List ℕ) (p : ℕ) (hp : p < l.length) (i : ℕ) (hi : i ≤ l[p] + 1) :
    (sig l)[2 * p + (l.take p).sum + i]? = (blk l[p])[i]? := by
  have hsplit : l = l.take p ++ (l[p] :: l.drop (p + 1)) := by
    simp
  have hlen : (sig (l.take p)).length = 2 * p + (l.take p).sum := by
    rw [sig_length, List.length_take, Nat.min_eq_left hp.le]
  have hs : sig l = sig (l.take p) ++ (blk l[p] ++ sig (l.drop (p + 1))) := by
    conv_lhs => rw [hsplit]
    rw [sig_append, show l[p] :: l.drop (p + 1) = [l[p]] ++ l.drop (p + 1) from rfl, sig_append]
    simp [sig]
  rw [hs, List.getElem?_append_right (by omega), hlen, Nat.add_sub_cancel_left,
    List.getElem?_append_left (by simp [blk]; omega)]

theorem w_block (p i : ℕ) (hi : i ≤ w p + 1) : w (st p + i) = (blk (w p))[i]?.getD 0 := by
  set k := p + 1
  have hpk : p < (Wl k).length := lt_of_lt_of_le (Nat.lt_succ_self p) (Wl_length _)
  have hl : ∀ j (h : j < (Wl k).length), (Wl k)[j] = w j := fun j h => w_eq h
  have h1 := sig_get (Wl k) p hpk i (by rw [hl]; exact hi)
  rw [take_sum _ p hpk.le hl, hl] at h1
  have h2 : (Wl (k + 1))[st p + i]? = (blk (w p))[i]? := by
    show (0 :: sig (Wl k))[st p + i]? = _
    rw [show st p + i = (2 * p + Λ p + i) + 1 by unfold st; ring, List.getElem?_cons_succ, h1]
  have h3 : i < (blk (w p)).length := by simp [blk]; omega
  rw [List.getElem?_eq_getElem h3] at h2
  rw [w_of_get h2, List.getElem?_eq_getElem h3]; rfl

theorem w_st (p : ℕ) : w (st p) = w p + 1 := by
  have := w_block p 0 (by omega); simpa [blk] using this

theorem w_st_add (p i : ℕ) (h1 : 1 ≤ i) (h2 : i ≤ w p + 1) : w (st p + i) = 0 := by
  rw [w_block p i h2]
  obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
  simp [blk, show i' < w p + 1 by omega]

/-! ### Block tiling -/

theorem st_mono {p q : ℕ} (h : p ≤ q) : st p ≤ st q := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => rw [st_succ]; omega

theorem cover (t : ℕ) (ht : 1 ≤ t) : ∃ p i, t = st p + i ∧ i ≤ w p + 1 := by
  induction t with
  | zero => omega
  | succ t ih =>
    rcases Nat.eq_zero_or_pos t with rfl | ht'
    · exact ⟨0, 0, by simp [st, Λ], by omega⟩
    · obtain ⟨p, i, rfl, hi⟩ := ih ht'
      by_cases h : i < w p + 1
      · exact ⟨p, i + 1, by ring, by omega⟩
      · exact ⟨p + 1, 0, by rw [st_succ]; omega, by omega⟩

theorem block_unique {p q i j : ℕ} (hi : i ≤ w p + 1) (hj : j ≤ w q + 1)
    (h : st p + i = st q + j) : p = q := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hpq | hpq
  · have := st_mono (show p + 1 ≤ q by omega); rw [st_succ] at this; omega
  · have := st_mono (show q + 1 ≤ p by omega); rw [st_succ] at this; omega

theorem block_start {t : ℕ} (h : w t ≠ 0) : ∃ p, t = st p := by
  have ht : 1 ≤ t := by
    by_contra hc; rw [show t = 0 by omega, w_zero] at h; exact h rfl
  obtain ⟨p, i, rfl, hi⟩ := cover t ht
  rcases Nat.eq_zero_or_pos i with rfl | hi0
  · exact ⟨p, rfl⟩
  · exact absurd (w_st_add p i hi0 hi) h

/-! ### Counting nonzero letters -/

/-- c n = number of nonzero letters among w 0 .. w (n-1). -/
def c (n : ℕ) : ℕ := ((range n).filter fun i => w i ≠ 0).card

theorem c_zero : c 0 = 0 := rfl

theorem c_succ (n : ℕ) : c (n + 1) = c n + if w n ≠ 0 then 1 else 0 := by
  unfold c
  rw [range_add_one, filter_insert]
  split_ifs with h
  · rw [card_insert_of_notMem (by simp)]
  · rfl

theorem c_one : c 1 = 0 := by rw [c_succ, c_zero, w_zero]; simp

theorem c_le (n : ℕ) : c n ≤ n := by
  unfold c; exact (card_filter_le _ _).trans (by simp)

theorem c_iter_zero (j : ℕ) : c^[j] 0 = 0 := by
  induction j with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply', ih, c_zero]

theorem c_block (p : ℕ) : ∀ j, j ≤ w p + 1 → c (st p + j + 1) = c (st p) + 1 := by
  intro j
  induction j with
  | zero => intro _; rw [add_zero, c_succ, w_st]; simp
  | succ j ih =>
    intro hj
    rw [show st p + (j + 1) + 1 = (st p + (j + 1)) + 1 by ring, c_succ,
      w_st_add p (j + 1) (by omega) hj, ← add_assoc, ih (by omega)]
    simp

theorem c_st (p : ℕ) : c (st p) = p := by
  induction p with
  | zero => simp [st, Λ, c_one]
  | succ p ih =>
    rw [st_succ, show st p + w p + 2 = st p + (w p + 1) + 1 by ring,
      c_block p (w p + 1) le_rfl, ih]

theorem Λ_block (p : ℕ) : ∀ j, j ≤ w p + 1 → Λ (st p + j + 1) = Λ (st p) + (w p + 1) := by
  intro j
  induction j with
  | zero => intro _; rw [add_zero, Λ, sum_range_succ, ← Λ, w_st]
  | succ j ih =>
    intro hj
    rw [show st p + (j + 1) + 1 = (st p + (j + 1)) + 1 by ring, Λ, sum_range_succ, ← Λ,
      w_st_add p (j + 1) (by omega) hj, ← add_assoc, ih (by omega)]; simp

theorem Λ_st (p : ℕ) : Λ (st p) = Λ p + p := by
  induction p with
  | zero => simp [st, Λ, w_zero]
  | succ p ih =>
    rw [st_succ, show st p + w p + 2 = st p + (w p + 1) + 1 by ring, Λ_block p _ le_rfl, ih,
      Λ, Λ, sum_range_succ]
    ring

/-- Parent property: a nonzero letter at t is the start of block c(t+1) - 1. -/
theorem c_parent {t : ℕ} (h : w t ≠ 0) : 1 ≤ c (t + 1) ∧ w (c (t + 1) - 1) + 1 = w t := by
  obtain ⟨p, rfl⟩ := block_start h
  have := c_block p 0 (by omega)
  rw [add_zero, c_st] at this
  rw [this, w_st]; simp

/-- c^[j] (u+1) - c^[j] u = [j ≤ w u]. -/
theorem c_iter_step (u : ℕ) : ∀ j,
    (j ≤ w u → c^[j] (u + 1) = c^[j] u + 1 ∧ w (c^[j] (u + 1) - 1) + j = w u) ∧
    (w u < j → c^[j] (u + 1) = c^[j] u) := by
  intro j
  induction j with
  | zero => exact ⟨fun _ => ⟨rfl, by simp⟩, fun h => absurd h (by omega)⟩
  | succ j ih =>
    refine ⟨fun hj => ?_, fun hj => ?_⟩
    · obtain ⟨h1, h2⟩ := ih.1 (by omega)
      set X := c^[j] (u + 1) with hX
      have hX1 : 1 ≤ X := by omega
      have hw : w (X - 1) ≠ 0 := by omega
      have hc := c_succ (X - 1)
      rw [show X - 1 + 1 = X by omega] at hc
      simp only [hw, ne_eq, not_false_eq_true, ↓reduceIte] at hc
      obtain ⟨hp1, hp2⟩ := c_parent hw
      rw [show X - 1 + 1 = X by omega] at hp1 hp2
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← hX]
      refine ⟨?_, by omega⟩
      rw [show c^[j] u = X - 1 by omega, hc]
    · rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      rcases Nat.lt_or_ge (w u) j with hlt | hge
      · rw [ih.2 hlt]
      · obtain ⟨h1, h2⟩ := ih.1 hge
        have hw : w (c^[j] (u + 1) - 1) = 0 := by omega
        have hc := c_succ (c^[j] (u + 1) - 1)
        rw [show c^[j] (u + 1) - 1 + 1 = c^[j] (u + 1) by omega, hw] at hc
        rw [hc, show c^[j] u = c^[j] (u + 1) - 1 by omega]; simp

/-- Exactly one block covers position t ≥ 1 from the left, unless t starts one. -/
theorem coverage (t : ℕ) (ht : 1 ≤ t) :
    ((Icc 1 t).filter fun j => j ≤ w (t - j)).card = if w t = 0 then 1 else 0 := by
  obtain ⟨p, i, rfl, hi⟩ := cover t ht
  have key : ∀ j ∈ Icc 1 (st p + i), j ≤ w (st p + i - j) ↔ j = i ∧ 1 ≤ i := by
    intro j hj
    rw [mem_Icc] at hj
    constructor
    · intro hle
      have hne : w (st p + i - j) ≠ 0 := by omega
      obtain ⟨q, hq⟩ := block_start hne
      rw [hq, w_st] at hle
      have := block_unique hi (show j ≤ w q + 1 from hle) (by omega)
      subst this
      omega
    · rintro ⟨rfl, -⟩
      rw [show st p + j - j = st p by omega, w_st]; omega
  rcases Nat.eq_zero_or_pos i with rfl | hi0
  · have hz : w (st p + 0) ≠ 0 := by rw [add_zero, w_st]; omega
    simp only [hz, ↓reduceIte]
    rw [card_eq_zero, filter_eq_empty_iff]
    intro j hj hle; have := (key j hj).mp hle; omega
  · simp only [w_st_add p i hi0 hi, ↓reduceIte]
    rw [card_eq_one]
    refine ⟨i, ?_⟩
    ext j
    simp only [mem_filter, mem_singleton]
    constructor
    · rintro ⟨hj, hle⟩; exact ((key j hj).mp hle).1
    · rintro rfl
      have hj : j ∈ Icc 1 (st p + j) := by rw [mem_Icc]; constructor <;> omega
      exact ⟨hj, (key j hj).mpr ⟨rfl, hi0⟩⟩

/-- The recurrence on ℕ: c (N+1) + Σ_{i=1..N} c^[i] (N+1-i) = N. -/
theorem rec_nat (N : ℕ) : c (N + 1) + ∑ i ∈ Icc 1 N, c^[i] (N + 1 - i) = N := by
  induction N with
  | zero => simp [c_one]
  | succ N ih =>
    rw [sum_Icc_succ_top (by omega), show N + 1 + 1 - (N + 1) = 1 by omega]
    have hlast : c^[N + 1] 1 = 0 := by
      rw [Function.iterate_succ_apply, c_one, c_iter_zero]
    have hstep : ∑ i ∈ Icc 1 N, c^[i] (N + 1 + 1 - i) =
        ∑ i ∈ Icc 1 N, c^[i] (N + 1 - i) + ∑ i ∈ Icc 1 N, if i ≤ w (N + 1 - i) then 1 else 0 := by
      rw [← sum_add_distrib]
      refine sum_congr rfl fun i hi => ?_
      rw [mem_Icc] at hi
      rw [show N + 1 + 1 - i = (N + 1 - i) + 1 by omega]
      split_ifs with h
      · exact (c_iter_step (N + 1 - i) i).1 h |>.1
      · rw [(c_iter_step (N + 1 - i) i).2 (by omega)]; simp
    have hcov := coverage (N + 1) (by omega)
    rw [card_filter, sum_Icc_succ_top (by omega), show N + 1 - (N + 1) = 0 by omega,
      w_zero] at hcov
    simp only [show ¬ (N + 1 ≤ 0) by omega, ↓reduceIte, add_zero] at hcov
    rw [hstep, hlast, add_zero, hcov, c_succ]
    split_ifs with h1 h2 <;> omega

/-! ### The OEIS recurrence over ℤ -/

/-- c extended by 0 to the integers. -/
def C (n : ℤ) : ℤ := c n.toNat

theorem C_nat_iter (m j : ℕ) : C^[j] (m : ℤ) = (c^[j] m : ℕ) := by
  induction j generalizing m with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ← ih]; simp [C]

theorem C_le_one {n : ℤ} (h : n ≤ 1) : C n = 0 := by
  unfold C
  rcases le_or_gt n 0 with h0 | h0
  · rw [Int.toNat_of_nonpos h0, c_zero]; rfl
  · rw [show n.toNat = 1 by omega, c_one]; rfl

/-- C satisfies the recurrence of A227145. -/
theorem C_rec (n : ℕ) (hn : 2 ≤ n) :
    C n = n - 1 - ∑ i ∈ Icc 1 n, C^[i] ((n : ℤ) - i) := by
  obtain ⟨N, rfl⟩ : ∃ N, n = N + 1 := ⟨n - 1, by omega⟩
  have h := rec_nat N
  rw [sum_Icc_succ_top (by omega)]
  have hcast : ∀ i ∈ Icc 1 N, C^[i] (((N + 1 : ℕ) : ℤ) - i) = (c^[i] (N + 1 - i) : ℕ) := by
    intro i hi
    rw [mem_Icc] at hi
    rw [show ((N + 1 : ℕ) : ℤ) - (i : ℤ) = ((N + 1 - i : ℕ) : ℤ) by push_cast [show i ≤ N + 1 by omega]; ring,
      C_nat_iter]
  rw [sum_congr rfl hcast, show ((N + 1 : ℕ) : ℤ) - ((N + 1 : ℕ) : ℤ) = ((0 : ℕ) : ℤ) by simp,
    C_nat_iter, c_iter_zero]
  unfold C
  simp only [Int.toNat_natCast]
  have : (∑ i ∈ Icc 1 N, ((c^[i] (N + 1 - i) : ℕ) : ℤ)) = ((∑ i ∈ Icc 1 N, c^[i] (N + 1 - i) : ℕ) : ℤ) := by
    push_cast; rfl
  rw [this]
  omega

/-- Any solution of the recurrence equals C. -/
theorem eq_C (a : ℤ → ℤ) (h0 : ∀ n : ℤ, n ≤ 1 → a n = 0)
    (hrec : ∀ n : ℕ, 2 ≤ n → a n = n - 1 - ∑ i ∈ Icc 1 n, a^[i] ((n : ℤ) - i)) :
    ∀ n : ℕ, a n = C n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.lt_or_ge n 2 with hn | hn
    · rw [h0 _ (by omega), C_le_one (by omega)]
    · have hall : ∀ x : ℤ, x < n → a x = C x := by
        intro x hx
        rcases le_or_gt x 0 with hx0 | hx0
        · rw [h0 x (by omega), C_le_one (by omega)]
        · have := ih x.toNat (by omega)
          rwa [Int.toNat_of_nonneg hx0.le] at this
      have hC : ∀ x : ℤ, x < n → C x < n := by
        intro x hx
        unfold C
        have := c_le x.toNat
        omega
      have hit : ∀ j, ∀ x : ℤ, x < n → a^[j] x = C^[j] x := by
        intro j
        induction j with
        | zero => intro x _; rfl
        | succ j ihj =>
          intro x hx
          rw [Function.iterate_succ_apply, Function.iterate_succ_apply, hall x hx]
          exact ihj _ (hC x hx)
      rw [hrec n hn, C_rec n hn]
      congr 1
      refine sum_congr rfl fun i hi => ?_
      rw [mem_Icc] at hi
      exact hit i _ (by omega)

/-! ### Fibonacci values -/

theorem c_st_pred (p : ℕ) (hp : 1 ≤ p) : c (st p - 1) = p ∧ Λ (st p - 1) = Λ p + p := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  have hz : w (st (q + 1) - 1) = 0 := by
    rw [st_succ, show st q + w q + 2 - 1 = st q + (w q + 1) by omega]
    exact w_st_add q _ (by omega) le_rfl
  have hc := c_succ (st (q + 1) - 1)
  have hl : Λ (st (q + 1) - 1 + 1) = Λ (st (q + 1) - 1) + w (st (q + 1) - 1) := by
    rw [Λ, sum_range_succ]; rfl
  have h1 : st (q + 1) - 1 + 1 = st (q + 1) := by rw [st_succ]; omega
  rw [h1, hz, c_st] at hc
  rw [h1, hz, Λ_st] at hl
  simp at hc
  exact ⟨hc.symm, by omega⟩

theorem fib_odd_step (k : ℕ) (h : Λ (Nat.fib (2 * k + 1)) = Nat.fib (2 * k)) :
    Λ (Nat.fib (2 * k + 3)) = Nat.fib (2 * k + 2) ∧ c (Nat.fib (2 * k + 3)) = Nat.fib (2 * k + 1) := by
  have e1 : Nat.fib (2 * k + 2) = Nat.fib (2 * k) + Nat.fib (2 * k + 1) := Nat.fib_add_two
  have e2 : Nat.fib (2 * k + 3) = Nat.fib (2 * k + 1) + Nat.fib (2 * k + 2) := Nat.fib_add_two
  have hp : 1 ≤ Nat.fib (2 * k + 1) := Nat.fib_pos.mpr (by omega)
  obtain ⟨h1, h2⟩ := c_st_pred _ hp
  have hst : st (Nat.fib (2 * k + 1)) - 1 = Nat.fib (2 * k + 3) := by unfold st; omega
  rw [hst] at h1 h2
  exact ⟨by omega, h1⟩

theorem fib_odd (k : ℕ) : Λ (Nat.fib (2 * k + 1)) = Nat.fib (2 * k) := by
  induction k with
  | zero => simp [Λ, w_zero]
  | succ k ih =>
    rw [show 2 * (k + 1) + 1 = 2 * k + 3 by ring, show 2 * (k + 1) = 2 * k + 2 by ring]
    exact (fib_odd_step k ih).1

theorem fib_even_step (k : ℕ) (h : Λ (Nat.fib (2 * k + 2)) + 1 = Nat.fib (2 * k + 1)) :
    Λ (Nat.fib (2 * k + 4)) + 1 = Nat.fib (2 * k + 3) ∧
      c (Nat.fib (2 * k + 4)) = Nat.fib (2 * k + 2) := by
  have e2 : Nat.fib (2 * k + 3) = Nat.fib (2 * k + 1) + Nat.fib (2 * k + 2) := Nat.fib_add_two
  have e3 : Nat.fib (2 * k + 4) = Nat.fib (2 * k + 2) + Nat.fib (2 * k + 3) := Nat.fib_add_two
  have hst : st (Nat.fib (2 * k + 2)) = Nat.fib (2 * k + 4) := by unfold st; omega
  have h1 := c_st (Nat.fib (2 * k + 2))
  have h2 := Λ_st (Nat.fib (2 * k + 2))
  rw [hst] at h1 h2
  exact ⟨by omega, h1⟩

theorem fib_even (k : ℕ) : Λ (Nat.fib (2 * k + 2)) + 1 = Nat.fib (2 * k + 1) := by
  induction k with
  | zero => simp [Λ, w_zero]
  | succ k ih =>
    rw [show 2 * (k + 1) + 2 = 2 * k + 4 by ring, show 2 * (k + 1) + 1 = 2 * k + 3 by ring]
    exact (fib_even_step k ih).1

theorem c_fib (m : ℕ) (hm : 2 ≤ m) : c (Nat.fib m) = Nat.fib (m - 2) := by
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' m
  · rcases Nat.lt_or_ge k 2 with hk | hk
    · obtain rfl : k = 1 := by omega
      simp [c_one]
    · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 2 := ⟨k - 2, by omega⟩
      rw [show 2 * (k' + 2) = 2 * k' + 4 by ring, (fib_even_step k' (fib_even k')).2]
      rfl
  · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [show 2 * (k' + 1) + 1 = 2 * k' + 3 by ring, (fib_odd_step k' (fib_odd k')).2]
    rfl

/-- Existence: the recurrence has a solution (so the hypotheses below are not vacuous). -/
theorem exists_solution : ∃ a : ℤ → ℤ, (∀ n : ℤ, n ≤ 1 → a n = 0) ∧
    ∀ n : ℕ, 2 ≤ n → a n = n - 1 - ∑ i ∈ Icc 1 n, a^[i] ((n : ℤ) - i) :=
  ⟨C, fun _ h => C_le_one h, C_rec⟩

theorem A227145_conjecture (a : ℤ → ℤ) (h0 : ∀ n : ℤ, n ≤ 1 → a n = 0)
    (hrec : ∀ n : ℕ, 2 ≤ n → a n = n - 1 - ∑ i ∈ Icc 1 n, a^[i] ((n : ℤ) - i))
    (m : ℕ) (hm : 2 ≤ m) : a (Nat.fib m) = Nat.fib (m - 2) := by
  rw [eq_C a h0 hrec, C]
  simp [c_fib m hm]
