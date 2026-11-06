import Mathlib

/-
OEIS A138684 (offset 1): first differences of A138683.  A138683 is the greedy
sequence 2, 3, 6, 7, 8, 12, ... : each term is the least integer above the
previous one whose sum with every earlier term is not a term of A001333
(1, 1, 3, 7, 17, 41, ...).  The entry's name says a(1) = 1, but its data and
the data of A138684 start at a(1) = 2; we follow the data (see README).

Conjecture (J. W. Layman, Nov 26 2011): with x(1) = 1, x(2) = 2,
x(n) = 2x(n-1) + x(n-2) and y(1) = 1, y(2) = 3, y(n) = y(n-1) + y(n-2):
a(x(k)) = y(k); a(n) = a(n - x(k)) for x(k) < n < 2x(k); a(n) = 1 for
2x(k) <= n < x(k+1).

Definitions.  `inS x` (by well-founded recursion): 2 <= x and no smaller
`inS y` has `IsQ (x + y)`, `IsQ v` = v is a value of `A001333`.
`A138683 n = Nat.nth inS (n - 1)`, `A138684 n = A138683 (n+1) - A138683 n`.
`A138683_greedy` and `A138683_unique`: this is the greedy sequence with
first term 2 (every sequence obeying the greedy rule with f 1 = 2 equals it).

Main theorems.
* `conjecture_false`: `¬ Shape yc`; a(12) = 6 while x(4) = 12, y(4) = 7.
* `A138684_shape`: `Shape zc`, i.e. the conjecture holds with y(k) replaced
  by z(1) = 1, z(k) = (A001333(k-1) + 5)/2 (k >= 2): 1, 3, 4, 6, 11, 23, 52.
  Parts: `A138684_at` (2 a(P k) = A001333(k-1) + 5), `A138684_mid`,
  `A138684_ones`, `A138684_one`; `xc_eq`: x(k) = Pell P k.

Route.  With r j = P 1 + ... + P j and q j = 2 r j + 1 (= A001333 (j+1)),
`rule`: for x in [r j + 1, r (j+1)] only q j can be a sum x + y with y < x,
so x is a term iff x >= q j or q j - x is not a term.  `reflect`, `copy`,
`gap`, `run`: on level j + 2 the terms are the earlier terms shifted by
2 P (j+2), preceded by a gap and followed by a run of P (j+1) consecutive
integers.  `inv`: exactly P (j+2) terms are <= r (j+2).  `s_copy`, `s_P`,
`s_run` translate to positions via `Nat.count` / `Nat.nth`.

Not checked in this file: agreement with the OEIS data terms
(certificate/check.py recomputes them from the same definition).
-/

namespace OEIS

/-- Pell numbers 0, 1, 2, 5, 12, 29, ... -/
def P : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | (n + 2) => 2 * P (n + 1) + P n

/-- A001333: 1, 1, 3, 7, 17, 41, ... -/
def A001333 : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | (n + 2) => 2 * A001333 (n + 1) + A001333 n

def IsQ (v : ℕ) : Prop := ∃ m, A001333 m = v

/-- `inS x`: x is a term of A138683. -/
def inS : ℕ → Prop
  | x => 2 ≤ x ∧ ∀ y, y < x → inS y → ¬ IsQ (x + y)
termination_by x => x

noncomputable def A138683 (n : ℕ) : ℕ := Nat.nth inS (n - 1)

noncomputable def A138684 (n : ℕ) : ℕ := A138683 (n + 1) - A138683 n

theorem inS_iff (x : ℕ) : inS x ↔ 2 ≤ x ∧ ∀ y, y < x → inS y → ¬ IsQ (x + y) := by
  rw [inS]

theorem two_le_of_inS {x : ℕ} (h : inS x) : 2 ≤ x := ((inS_iff x).1 h).1


/-! ## Pell facts -/

/-- `omega` after normalising `j + 2 + 1` to `j + 3` and unfolding `q`. -/
macro "nomega" : tactic =>
  `(tactic| ((try simp only [Nat.add_assoc, Nat.reduceAdd] at *) <;> omega))

/-- r j = P 1 + ... + P j. -/
def r : ℕ → ℕ
  | 0 => 0
  | (j + 1) => r j + P (j + 1)

theorem P_succ_succ (n : ℕ) : P (n + 2) = 2 * P (n + 1) + P n := rfl

theorem r_succ (j : ℕ) : r (j + 1) = r j + P (j + 1) := rfl

theorem P_pos (n : ℕ) : 0 < P (n + 1) := by
  induction n with
  | zero => simp [P]
  | succ n ih => rw [P_succ_succ]; nomega

theorem P_double (n : ℕ) : 2 * P (n + 1) ≤ P (n + 2) := by
  rw [P_succ_succ]; nomega

theorem q_eq (j : ℕ) : P (j + 1) + P j = 2 * r j + 1 := by
  induction j with
  | zero => simp [P, r]
  | succ j ih => rw [P_succ_succ, r_succ]; nomega

theorem r_lt (j : ℕ) : r j < P (j + 1) := by
  induction j with
  | zero => simp [P, r]
  | succ j ih => have := P_double j; rw [r_succ]; nomega

theorem r_ge (j : ℕ) : j ≤ r j := by
  induction j with
  | zero => simp [r]
  | succ j ih => have := P_pos j; rw [r_succ]; nomega

theorem A001333_succ (j : ℕ) : A001333 (j + 1) = P (j + 1) + P j := by
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    match j, ih with
    | 0, _ => simp [A001333, P]
    | 1, _ => simp [A001333, P]
    | (j + 2), ih =>
      have h1 := ih (j + 1) (by nomega)
      have h0 := ih j (by nomega)
      show 2 * A001333 (j + 2) + A001333 (j + 1) = _
      rw [h1, h0, P_succ_succ (j + 1), P_succ_succ j]
      ring

/-- q j = P (j+1) + P j = 2 r j + 1 = A001333 (j+1): 1, 3, 7, 17, 41, ... -/
def q (j : ℕ) : ℕ := 2 * r j + 1

macro_rules
  | `(tactic| nomega) =>
    `(tactic| ((try simp only [Nat.add_assoc, Nat.reduceAdd] at *) <;> (try simp only [q] at *) <;> omega))

theorem q_strictMono : StrictMono q := by
  apply strictMono_nat_of_lt_succ
  intro j; have := P_pos j; simp [q, r_succ]; nomega

theorem isQ_iff (v : ℕ) : IsQ v ↔ ∃ j, q j = v := by
  constructor
  · rintro ⟨m, hm⟩
    cases m with
    | zero => exact ⟨0, by simp [q, r] at *; simp [A001333] at hm; nomega⟩
    | succ m => exact ⟨m, by rw [A001333_succ, q_eq] at hm; simpa [q] using hm⟩
  · rintro ⟨j, hj⟩
    exact ⟨j + 1, by rw [A001333_succ, q_eq]; simpa [q] using hj⟩

/-! ## The local rule -/

/-- On `[r j + 1, r (j+1)]` only `q j` matters. -/
theorem rule (j x : ℕ) (h1 : r j + 1 ≤ x) (h2 : x ≤ r (j + 1)) (h3 : 2 ≤ x) :
    inS x ↔ (x < q j → ¬ inS (q j - x)) := by
  rw [inS_iff]
  constructor
  · rintro ⟨_, h⟩ hlt hS
    have hy : q j - x < x := by simp only [q]; nomega
    exact h _ hy hS ((isQ_iff _).2 ⟨j, by nomega⟩)
  · intro h
    refine ⟨h3, fun y hy hS hQ => ?_⟩
    obtain ⟨i, hi⟩ := (isQ_iff _).1 hQ
    have hy2 := two_le_of_inS hS
    have hr := r_succ j
    have hPj := r_lt (j + 1)
    have hij : i < j + 1 := by
      by_contra hc
      have := q_strictMono.monotone (show j + 1 ≤ i by nomega)
      simp only [q] at this hi; nomega
    rcases Nat.lt_or_ge i j with hlt | hge
    · obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by nomega⟩
      have hm := q_strictMono.monotone (show i ≤ j' by nomega)
      have := r_lt j'
      have := r_succ j'
      simp only [q] at hm hi; nomega
    · have hij' : i = j := by nomega
      subst hij'
      have hx : x < q i := by nomega
      have : q i - x = y := by nomega
      exact h hx (this ▸ hS)

theorem run (j x : ℕ) (h1 : q j ≤ x) (h2 : x ≤ r (j + 1)) (h3 : 2 ≤ x) : inS x := by
  rw [rule j x (by simp only [q] at h1; nomega) h2 h3]
  intro h; nomega

/-- Reflection about `q (j+1)` on `[1, r (j+2)]`. -/
theorem reflect (j z : ℕ) (h1 : 1 ≤ z) (h2 : z ≤ r (j + 2)) :
    inS z ↔ ¬ (z < q (j + 1) ∧ inS (q (j + 1) - z)) := by
  have hP := P_pos j
  have hr1 := r_succ j
  have hr2 := r_succ (j + 1)
  have hl := r_lt (j + 1)
  rcases Nat.lt_or_ge (r (j + 1)) z with hz | hz
  · rw [rule (j + 1) z (by nomega) h2 (by nomega)]
    tauto
  · have hw := rule (j + 1) (q (j + 1) - z) (by simp only [q]; nomega)
      (by simp only [q]; nomega) (by simp only [q]; nomega)
    have e : q (j + 1) - (q (j + 1) - z) = z := by simp only [q]; nomega
    rw [e] at hw
    have hlt : q (j + 1) - z < q (j + 1) := by simp only [q]; nomega
    have hlt2 : z < q (j + 1) := by simp only [q]; nomega
    constructor
    · rintro hz' ⟨_, hw'⟩; exact (hw.1 hw') hlt hz'
    · intro h
      by_contra hn
      exact h ⟨hlt2, hw.2 (fun _ => hn)⟩

/-- Self-similarity: shift by `2 P (j+2)`. -/
theorem copy (j z : ℕ) (h1 : 1 ≤ z) (h2 : z ≤ r (j + 2)) :
    inS (z + 2 * P (j + 2)) ↔ inS z := by
  have hP3 := P_succ_succ (j + 1)
  have hr := r_succ (j + 2)
  have hr2 := r_succ (j + 1)
  have hl := r_lt (j + 1)
  have hq1 := q_eq (j + 1)
  have hq2 := q_eq (j + 2)
  rw [rule (j + 2) _ (by nomega) (by nomega) (by nomega), reflect j z h1 h2]
  have e1 : q (j + 2) - (z + 2 * P (j + 2)) = q (j + 1) - z := by simp only [q]; nomega
  have e2 : z + 2 * P (j + 2) < q (j + 2) ↔ z < q (j + 1) := by simp only [q]; nomega
  rw [e1, e2]
  tauto

theorem gap (j x : ℕ) (h1 : r (j + 2) + 1 ≤ x) (h2 : x ≤ 2 * P (j + 2)) : ¬ inS x := by
  have hP3 := P_succ_succ (j + 1)
  have hr := r_succ (j + 2)
  have hr2 := r_succ (j + 1)
  have hl := r_lt (j + 1)
  have hq1 := q_eq (j + 1)
  have hq2 := q_eq (j + 2)
  have hPj := P_pos j
  rw [rule (j + 2) x (by nomega) (by nomega) (by nomega)]
  intro h
  apply h (by simp only [q]; nomega)
  apply run (j + 1) <;> nomega

theorem inS_r (j : ℕ) : inS (r (j + 2)) := by
  have hr2 := r_succ (j + 1)
  have hl := r_lt (j + 1)
  have hPj := P_pos j
  have hr1 := r_succ j
  apply run (j + 1) <;> nomega

theorem infinite_inS : {x | inS x}.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro a
  exact ⟨r (a + 3), inS_r (a + 1), by have := r_ge (a + 3); nomega⟩

theorem not_inS_zero : ¬ inS 0 := fun h => by have := two_le_of_inS h; nomega
theorem not_inS_one : ¬ inS 1 := fun h => by have := two_le_of_inS h; nomega

theorem inS_two : inS 2 := by
  rw [rule 1 2 (by simp [r, P]) (by simp [r, P]) le_rfl]
  intro _; simp [q, r, P]; exact not_inS_one

/-! ## Counting -/

open Classical in
noncomputable def C (v : ℕ) : ℕ := Nat.count inS v

theorem C_succ_pos {v : ℕ} (h : inS v) : C (v + 1) = C v + 1 := by
  classical
  simp only [C]; rw [Nat.count_succ]; simp [h]

theorem C_succ_neg {v : ℕ} (h : ¬ inS v) : C (v + 1) = C v := by
  classical
  simp only [C]; rw [Nat.count_succ]; simp [h]

theorem C_zero : C 0 = 0 := by simp [C]
theorem C_one : C 1 = 0 := by rw [C_succ_neg not_inS_zero, C_zero]
theorem C_two : C 2 = 0 := by rw [C_succ_neg not_inS_one, C_one]

theorem nth_of_C {v : ℕ} (h : inS v) : Nat.nth inS (C v) = v := by
  classical
  simp only [C]; exact Nat.nth_count h

theorem C_nth (i : ℕ) : C (Nat.nth inS i) = i := by
  classical
  simp only [C]; exact Nat.count_nth_of_infinite infinite_inS i

theorem inS_nth (i : ℕ) : inS (Nat.nth inS i) := Nat.nth_mem_of_infinite infinite_inS i

theorem nth_lt_of_lt_C {i v : ℕ} (h : i < C v) : Nat.nth inS i < v := by
  classical
  simp only [C] at h; exact Nat.nth_lt_of_lt_count h

/-- Counts on the gap, the copy and the run of level `j + 2`. -/
theorem gapC (j : ℕ) (hI : C (r (j + 2) + 1) = P (j + 2)) :
    ∀ i, r (j + 2) + 1 + i ≤ 2 * P (j + 2) + 1 → C (r (j + 2) + 1 + i) = P (j + 2) := by
  intro i
  induction i with
  | zero => intro _; simpa using hI
  | succ i ih =>
    intro hi
    rw [show r (j + 2) + 1 + (i + 1) = (r (j + 2) + 1 + i) + 1 by nomega,
      C_succ_neg (gap j _ (by nomega) (by nomega))]
    exact ih (by nomega)

theorem copyC (j : ℕ) (hI : C (r (j + 2) + 1) = P (j + 2)) :
    ∀ d, d ≤ r (j + 2) → C (2 * P (j + 2) + 1 + d) = P (j + 2) + C (1 + d) := by
  have hl := r_lt (j + 1)
  have hr2 := r_succ (j + 1)
  have hP := P_double (j + 1)
  have h0 : C (2 * P (j + 2) + 1) = P (j + 2) := by
    have := gapC j hI (2 * P (j + 2) - r (j + 2)) (by nomega)
    rwa [show r (j + 2) + 1 + (2 * P (j + 2) - r (j + 2)) = 2 * P (j + 2) + 1 by nomega] at this
  intro d
  induction d with
  | zero => intro _; simpa [C_one] using h0
  | succ d ih =>
    intro hd
    have hc := copy j (1 + d) (by nomega) (by nomega)
    rw [show 1 + d + 2 * P (j + 2) = 2 * P (j + 2) + 1 + d by nomega] at hc
    have ih' := ih (by nomega)
    rw [show 2 * P (j + 2) + 1 + (d + 1) = (2 * P (j + 2) + 1 + d) + 1 by nomega,
      show 1 + (d + 1) = (1 + d) + 1 by nomega]
    by_cases hS : inS (1 + d)
    · rw [C_succ_pos (hc.2 hS), C_succ_pos hS, ih']; nomega
    · rw [C_succ_neg (fun h => hS (hc.1 h)), C_succ_neg hS, ih']

theorem copyC' (j : ℕ) (hI : C (r (j + 2) + 1) = P (j + 2)) (z : ℕ) (h1 : 1 ≤ z)
    (h2 : z ≤ r (j + 2) + 1) : C (2 * P (j + 2) + z) = P (j + 2) + C z := by
  have := copyC j hI (z - 1) (by nomega)
  rwa [show 2 * P (j + 2) + 1 + (z - 1) = 2 * P (j + 2) + z by nomega,
    show 1 + (z - 1) = z by nomega] at this

theorem runC (j : ℕ) (hI : C (r (j + 2) + 1) = P (j + 2)) :
    ∀ i, i ≤ P (j + 1) →
      C (r (j + 2) + 2 * P (j + 2) + 1 + i) = 2 * P (j + 2) + i := by
  have hl := r_lt (j + 1)
  have hr2 := r_succ (j + 1)
  have hr3 := r_succ (j + 2)
  have hP3 := P_succ_succ (j + 1)
  have hq := q_eq (j + 2)
  intro i
  induction i with
  | zero =>
    intro _
    have := copyC' j hI (r (j + 2) + 1) (by nomega) le_rfl
    rw [hI] at this
    rw [show r (j + 2) + 2 * P (j + 2) + 1 + 0 = 2 * P (j + 2) + (r (j + 2) + 1) by nomega, this]
    nomega
  | succ i ih =>
    intro hi
    have ih' := ih (by nomega)
    rw [show r (j + 2) + 2 * P (j + 2) + 1 + (i + 1)
        = (r (j + 2) + 2 * P (j + 2) + 1 + i) + 1 by nomega,
      C_succ_pos (run (j + 2) _ (by nomega) (by nomega) (by nomega)), ih']
    nomega

theorem inv (j : ℕ) : C (r (j + 2) + 1) = P (j + 2) := by
  induction j with
  | zero =>
    have h3 : inS 3 := run 1 3 (by simp [q, r, P]) (by simp [r, P]) (by nomega)
    show C 4 = 2
    rw [C_succ_pos h3, C_succ_pos inS_two, C_two]
  | succ j ih =>
    have := runC j ih (P (j + 1)) le_rfl
    have hr3 := r_succ (j + 2)
    have hP3 := P_succ_succ (j + 1)
    rw [show r (j + 2) + 2 * P (j + 2) + 1 + P (j + 1) = r (j + 3) + 1 by nomega] at this
    rw [this, P_succ_succ (j + 1)]

theorem C_lt {y v : ℕ} (hy : inS y) (h : y < v) : C y < C v := by
  classical
  simp only [C]; exact Nat.count_strict_mono hy h

/-! ## Positions -/

theorem s_copy (j m : ℕ) (h1 : 1 ≤ m) (h2 : m ≤ P (j + 2)) :
    A138683 (m + P (j + 2)) = A138683 m + 2 * P (j + 2) := by
  have hI := inv j
  simp only [A138683]
  have hv := inS_nth (m - 1)
  have hC := C_nth (m - 1)
  have hlt := nth_lt_of_lt_C (show m - 1 < C (r (j + 2) + 1) by rw [hI]; nomega)
  have h2v := two_le_of_inS hv
  have hc := (copy j _ (by nomega) (by nomega)).2 hv
  have hC2 := copyC' j hI (Nat.nth inS (m - 1)) (by nomega) (by nomega)
  rw [add_comm] at hc
  have := nth_of_C hc
  rw [hC2, hC] at this
  rw [show m + P (j + 2) - 1 = P (j + 2) + (m - 1) by nomega, this]
  ring

theorem s_P (j : ℕ) : A138683 (P (j + 2)) = r (j + 2) := by
  have hI := inv j
  rw [C_succ_pos (inS_r j)] at hI
  have := nth_of_C (inS_r j)
  simp only [A138683]
  rwa [show P (j + 2) - 1 = C (r (j + 2)) by nomega]

theorem s_one : A138683 1 = 2 := by
  have := nth_of_C inS_two
  rw [C_two] at this
  simpa [A138683] using this

theorem s_two : A138683 2 = 3 := by
  have h3 : inS 3 := run 1 3 (by simp [q, r, P]) (by simp [r, P]) (by nomega)
  have := nth_of_C h3
  rw [C_succ_pos inS_two, C_two] at this
  simpa [A138683] using this

theorem s_run (j i : ℕ) (hi : i ≤ P (j + 1)) :
    A138683 (2 * P (j + 2) + i) = r (j + 2) + 2 * P (j + 2) + i := by
  cases i with
  | zero =>
    have := s_copy j (P (j + 2)) (by have := P_pos (j + 1); nomega) le_rfl
    rw [s_P] at this
    rw [show 2 * P (j + 2) + 0 = P (j + 2) + P (j + 2) by nomega, this]
    simp
  | succ i =>
    have hl := r_lt (j + 1)
    have hr2 := r_succ (j + 1)
    have hr3 := r_succ (j + 2)
    have hP3 := P_succ_succ (j + 1)
    have hq := q_eq (j + 2)
    have hC := runC j (inv j) i (by nomega)
    have hS : inS (r (j + 2) + 2 * P (j + 2) + 1 + i) :=
      run (j + 2) _ (by nomega) (by nomega) (by nomega)
    have := nth_of_C hS
    rw [hC] at this
    simp only [A138683]
    rw [show 2 * P (j + 2) + (i + 1) - 1 = 2 * P (j + 2) + i by nomega, this]
    nomega

/-! ## Main theorems -/

theorem A138684_one : A138684 1 = 1 := by
  show A138683 2 - A138683 1 = 1
  rw [s_one, s_two]

/-- The value at `n = P k`, `k ≥ 2`: `2 a(P k) = A001333 (k-1) + 5`. -/
theorem A138684_at (j : ℕ) : 2 * A138684 (P (j + 2)) = A001333 (j + 1) + 5 := by
  have h := s_copy j 1 le_rfl (by have := P_pos (j + 1); nomega)
  rw [s_one, add_comm] at h
  simp only [A138684]
  rw [h, s_P, A001333_succ]
  have hq := q_eq (j + 2)
  have hP3 := P_succ_succ (j + 1)
  have hP2 := P_succ_succ j
  have hl := r_lt (j + 1)
  have hr2 := r_succ (j + 1)
  nomega

theorem A138684_mid (j n : ℕ) (h1 : P (j + 2) < n) (h2 : n < 2 * P (j + 2)) :
    A138684 n = A138684 (n - P (j + 2)) := by
  simp only [A138684]
  have e1 := s_copy j (n - P (j + 2)) (by nomega) (by nomega)
  have e2 := s_copy j (n - P (j + 2) + 1) (by nomega) (by nomega)
  rw [show n - P (j + 2) + P (j + 2) = n by nomega] at e1
  rw [show n - P (j + 2) + 1 + P (j + 2) = n + 1 by nomega] at e2
  rw [e1, e2]
  nomega

theorem A138684_ones (j n : ℕ) (h1 : 2 * P (j + 2) ≤ n) (h2 : n < P (j + 3)) :
    A138684 n = 1 := by
  have hP3 := P_succ_succ (j + 1)
  simp only [A138684]
  have e1 := s_run j (n - 2 * P (j + 2)) (by nomega)
  have e2 := s_run j (n - 2 * P (j + 2) + 1) (by nomega)
  rw [show 2 * P (j + 2) + (n - 2 * P (j + 2)) = n by nomega] at e1
  rw [show 2 * P (j + 2) + (n - 2 * P (j + 2) + 1) = n + 1 by nomega] at e2
  rw [e1, e2]
  nomega

/-! ## The conjecture as stated, and its corrected form -/

/-- Layman's x: x(1) = 1, x(2) = 2, x(n) = 2 x(n-1) + x(n-2) (x 0 unused). -/
def xc : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | (n + 3) => 2 * xc (n + 2) + xc (n + 1)

/-- Layman's y: y(1) = 1, y(2) = 3, y(n) = y(n-1) + y(n-2) (y 0 unused). -/
def yc : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | 2 => 3
  | (n + 3) => yc (n + 2) + yc (n + 1)

/-- The conjecture in the entry, for a value sequence `v` at the points `x(k)`. -/
def Shape (v : ℕ → ℕ) : Prop :=
  ∀ k n, 1 ≤ k →
    (n = xc k → A138684 n = v k) ∧
    (xc k < n → n < 2 * xc k → A138684 n = A138684 (n - xc k)) ∧
    (2 * xc k ≤ n → n < xc (k + 1) → A138684 n = 1)

/-- Corrected values: z(1) = 1 and z(k) = (A001333(k-1) + 5)/2 for k ≥ 2. -/
def zc (k : ℕ) : ℕ := if k ≤ 1 then 1 else (A001333 (k - 1) + 5) / 2

theorem xc_eq (k : ℕ) : xc (k + 1) = P (k + 1) := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    match k, ih with
    | 0, _ => rfl
    | 1, _ => rfl
    | (k + 2), ih =>
      show 2 * xc (k + 2) + xc (k + 1) = 2 * P (k + 2) + P (k + 1)
      rw [ih (k + 1) (by omega), ih k (by omega)]

/-- Layman's conjecture (Nov 26 2011) is false: a(12) = 6, while x(4) = 12, y(4) = 7. -/
theorem conjecture_false : ¬ Shape yc := by
  intro h
  have h12 := (h 4 12 (by omega)).1 rfl
  have := A138684_at 2
  rw [show P (2 + 2) = 12 from rfl, show A001333 (2 + 1) = 7 from rfl] at this
  rw [show yc 4 = 7 from rfl] at h12
  omega

/-- The corrected statement holds for every k ≥ 1. -/
theorem A138684_shape : Shape zc := by
  intro k n hk
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  rw [xc_eq, show k + 1 + 1 = k + 2 from rfl, xc_eq]
  cases k with
  | zero =>
    refine ⟨fun hn => ?_, fun h1 h2 => ?_, fun h1 h2 => ?_⟩
    · subst hn; simpa [zc, P] using A138684_one
    · simp [P] at h1 h2; omega
    · simp [P] at h1 h2; omega
  | succ j =>
    refine ⟨fun hn => ?_, fun h1 h2 => A138684_mid j n h1 h2, fun h1 h2 => A138684_ones j n h1 h2⟩
    subst hn
    have := A138684_at j
    simp only [zc, show ¬ (j + 1 + 1 ≤ 1) by omega, ite_false, show j + 1 + 1 - 1 = j + 1 by omega]
    nomega

/-! ## A138683 is the greedy sequence of the entry -/

theorem A138683_greedy (n : ℕ) (hn : 1 ≤ n) :
    IsLeast {m | A138683 n < m ∧ ∀ i, 1 ≤ i → i ≤ n → ¬ IsQ (A138683 i + m)}
      (A138683 (n + 1)) := by
  simp only [A138683, show n + 1 - 1 = n by omega]
  have hmono := Nat.nth_strictMono infinite_inS
  refine ⟨⟨hmono (by omega), fun i hi1 hi2 hQ => ?_⟩, fun m ⟨hm1, hm2⟩ => ?_⟩
  · have hS := (inS_iff _).1 (inS_nth n)
    exact hS.2 (Nat.nth inS (i - 1)) (hmono (show i - 1 < n by omega)) (inS_nth _)
      (by rwa [add_comm])
  · by_contra hlt
    rw [not_le] at hlt
    have h2 := two_le_of_inS (inS_nth (n - 1))
    have hmS : inS m := by
      rw [inS_iff]
      refine ⟨by omega, fun y hy hyS hQ => ?_⟩
      have hCy := C_lt hyS (lt_trans hy hlt)
      rw [C_nth] at hCy
      have := hm2 (C y + 1) (by omega) (by omega)
      rw [show C y + 1 - 1 = C y by omega, nth_of_C hyS, add_comm] at this
      exact this hQ
    have a1 := C_lt (inS_nth _) hm1
    have a2 := C_lt hmS hlt
    rw [C_nth] at a1 a2
    omega

/-- Any sequence with f 1 = 2 that follows the greedy rule of the entry is A138683
(on n ≥ 1). -/
theorem A138683_unique (f : ℕ → ℕ) (h1 : f 1 = 2)
    (hg : ∀ n, 1 ≤ n →
      IsLeast {m | f n < m ∧ ∀ i, 1 ≤ i → i ≤ n → ¬ IsQ (f i + m)} (f (n + 1))) :
    ∀ n, 1 ≤ n → f n = A138683 n := by
  intro n hn
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0; rw [h1, s_one]
    · have e : {m | f n < m ∧ ∀ i, 1 ≤ i → i ≤ n → ¬ IsQ (f i + m)}
          = {m | A138683 n < m ∧ ∀ i, 1 ≤ i → i ≤ n → ¬ IsQ (A138683 i + m)} := by
        ext m
        simp only [Set.mem_ofPred_eq]
        rw [ih n (by omega) hpos]
        constructor
        · rintro ⟨a, b⟩; exact ⟨a, fun i hi1 hi2 => by rw [← ih i (by omega) hi1]; exact b i hi1 hi2⟩
        · rintro ⟨a, b⟩; exact ⟨a, fun i hi1 hi2 => by rw [ih i (by omega) hi1]; exact b i hi1 hi2⟩
      have := hg n hpos
      rw [e] at this
      exact this.unique (A138683_greedy n hpos)
