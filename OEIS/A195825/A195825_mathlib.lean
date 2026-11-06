import Mathlib

/-
OEIS A195825: square array T(n,k), n >= 0, k >= 1; column k has g.f.
1 / Σ_{j ∈ ℤ} (-1)^j q^{(m j^2 - (m-2) j)/2}, m = k + 2 (generalized (k+4)-gonal numbers).
Conjecture (O. E. Pol, 2012): column k has ⌈k/2⌉ plateaus, with lengths k+1, k-1, k-3, ...
(down to 2 for odd k, 3 for even k), and their levels are the first terms of A210843 (the levels
of the plateaus as k → ∞).

Model used here.  By the Jacobi triple product the g.f. of column k is
Π_{n ≥ 1} 1/((1-q^{mn})(1-q^{mn-1})(1-q^{mn-m+1})), so T(n,k) is the number of partitions of n
into parts ≡ 0, ±1 (mod m): `T m n` below (Mathlib `Nat.Partition`).  The triple product step
is NOT checked in this file (certificate/check.py compares both for k ≤ 40, n ≤ 1500).

Main theorems.
* `flat_iff c n`: with m = c + 3 (k = c + 1), T(n+1) = T(n) iff
  A(m+1) ≤ n and n + 2 ≤ (A+1)(m-1) for some A.  So the maximal runs of equal terms are
  [A(m+1), (A+1)(m-1) - 1], of length k + 1 - 2A, for each A with k + 1 - 2A ≥ 2, and the
  column is strictly increasing elsewhere.
* `level_const A k`: for k ≥ 2A + 1 the level T_{k+2}(A(k+3)) of plateau A equals
  T_{2A+3}(A(2A+4)), independent of k; hence it is the k → ∞ limit, which is how A210843
  defines its (A+1)-th term.
Route: `T_succ` (T(n+1) = T(n) + D(n+1), D counts partitions without part 1), `D_pos_iff`
(n has a partition into parts ≡ 0, ±1 mod m, none 1, iff A(m-1) ≤ n ≤ A(m+1) for some A ≥ 1),
`level_step` (bijection `Φ`/`Ψ`: a part a m + e ↦ a (m+1) + e, e ∈ {-1,0,1}, refilled with 1s).
Checked: all of the above.  Not checked: the Jacobi triple product step; the numerical values
of A210843 (certificate/check.py: partial sums of A000716).
-/

namespace OEIS_A195825

open Finset

/-- Parts allowed in column k (m = k + 2): residues 0, 1, m - 1 mod m. -/
def good (m q : ℕ) : Prop := q % m = 0 ∨ q % m = 1 ∨ q % m = m - 1

instance (m q : ℕ) : Decidable (good m q) := by unfold good; infer_instance

/-- Number of partitions of n into parts ≡ 0, ±1 (mod m). -/
def T (m n : ℕ) : ℕ := (univ.filter (fun p : n.Partition => ∀ i ∈ p.parts, good m i)).card

/-- Number of such partitions of n with no part 1. -/
def D (m n : ℕ) : ℕ :=
  (univ.filter (fun p : n.Partition => (∀ i ∈ p.parts, good m i) ∧ 1 ∉ p.parts)).card

theorem good_one (m : ℕ) (hm : 3 ≤ m) : good m 1 := by
  right; left; exact Nat.mod_eq_of_lt (by omega)

/-- Remove one part 1. -/
def dropOne {n : ℕ} (p : (n + 1).Partition) (h : 1 ∈ p.parts) : n.Partition where
  parts := p.parts.erase 1
  parts_pos hi := p.parts_pos (Multiset.mem_of_mem_erase hi)
  parts_sum := by
    have := Multiset.sum_erase h
    rw [p.parts_sum] at this
    omega

/-- Add one part 1. -/
def addOne {n : ℕ} (q : n.Partition) : (n + 1).Partition where
  parts := 1 ::ₘ q.parts
  parts_pos hi := by
    rcases Multiset.mem_cons.mp hi with h | h
    · omega
    · exact q.parts_pos h
  parts_sum := by rw [Multiset.sum_cons, q.parts_sum]; omega

theorem T_succ (m n : ℕ) (hm : 3 ≤ m) : T m (n + 1) = T m n + D m (n + 1) := by
  unfold T D
  rw [← Finset.card_filter_add_card_filter_not
    (s := univ.filter (fun p : (n + 1).Partition => ∀ i ∈ p.parts, good m i))
    (fun p : (n + 1).Partition => 1 ∈ p.parts)]
  rw [Finset.filter_filter, Finset.filter_filter]
  congr 1
  · apply Finset.card_bij' (fun p hp => dropOne p (Finset.mem_filter.mp hp).2.2)
      (fun q _ => addOne q)
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
      intro i hi
      exact hp.1 i (Multiset.mem_of_mem_erase hi)
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
      apply Nat.Partition.ext
      exact Multiset.cons_erase hp.2
    · intro q _
      apply Nat.Partition.ext
      exact Multiset.erase_cons_head 1 q.parts
    · intro q hq
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
      refine ⟨?_, Multiset.mem_cons_self 1 q.parts⟩
      intro i hi
      rcases Multiset.mem_cons.mp hi with h | h
      · rw [h]; exact good_one m hm
      · exact hq i h

/-- One part q ≥ 2 of residue 0, ±1 mod m (m = c + 3) lies in [a(m-1), a(m+1)] for some a ≥ 1. -/
theorem part_bound (c q : ℕ) (hq : good (c + 3) q) (h2 : 2 ≤ q) :
    ∃ a, 1 ≤ a ∧ a * (c + 2) ≤ q ∧ q ≤ a * (c + 4) := by
  have hdm := Nat.div_add_mod q (c + 3)
  obtain ⟨t, ht'⟩ : ∃ t, t = q / (c + 3) := ⟨_, rfl⟩
  rw [← ht'] at hdm
  rcases hq with h | h | h
  · rw [h] at hdm
    refine ⟨t, ?_, ?_, ?_⟩
    · rcases Nat.eq_zero_or_pos t with ht | ht
      · rw [ht] at hdm; omega
      · exact ht
    · nlinarith
    · nlinarith
  · rw [h] at hdm
    refine ⟨t, ?_, ?_, ?_⟩
    · rcases Nat.eq_zero_or_pos t with ht | ht
      · rw [ht] at hdm; omega
      · exact ht
    · nlinarith
    · have : 1 ≤ t := by
        rcases Nat.eq_zero_or_pos t with ht | ht
        · rw [ht] at hdm; omega
        · exact ht
      nlinarith
  · rw [h] at hdm
    refine ⟨t + 1, by omega, ?_, ?_⟩
    · have : c + 3 - 1 = c + 2 := by omega
      rw [this] at hdm; nlinarith
    · have : c + 3 - 1 = c + 2 := by omega
      rw [this] at hdm; nlinarith

theorem sum_bound (c : ℕ) (s : Multiset ℕ) (hs : ∀ q ∈ s, good (c + 3) q ∧ 2 ≤ q) :
    ∃ A, Multiset.card s ≤ A ∧ A * (c + 2) ≤ s.sum ∧ s.sum ≤ A * (c + 4) := by
  induction s using Multiset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | cons q s ih =>
    obtain ⟨A, h1, h2, h3⟩ := ih (fun x hx => hs x (Multiset.mem_cons_of_mem hx))
    obtain ⟨a, ha1, ha2, ha3⟩ := part_bound c q (hs q (Multiset.mem_cons_self q s)).1
      (hs q (Multiset.mem_cons_self q s)).2
    refine ⟨A + a, ?_, ?_, ?_⟩
    · simp; omega
    · simp; nlinarith
    · simp; nlinarith

/-- n ≥ 1 has a partition into parts ≡ 0, ±1 (mod m), none equal to 1, iff
A(m-1) ≤ n ≤ A(m+1) for some A ≥ 1 (here m = c + 3). -/
theorem D_pos_iff (c n : ℕ) (hn : 1 ≤ n) :
    0 < D (c + 3) n ↔ ∃ A, 1 ≤ A ∧ A * (c + 2) ≤ n ∧ n ≤ A * (c + 4) := by
  constructor
  · intro h
    obtain ⟨p, hp⟩ := Finset.card_pos.mp h
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    have hs : ∀ q ∈ p.parts, good (c + 3) q ∧ 2 ≤ q := by
      intro q hq
      refine ⟨hp.1 q hq, ?_⟩
      have := p.parts_pos hq
      have : q ≠ 1 := fun e => hp.2 (e ▸ hq)
      omega
    obtain ⟨A, h1, h2, h3⟩ := sum_bound c p.parts hs
    rw [p.parts_sum] at h2 h3
    refine ⟨A, ?_, h2, h3⟩
    rcases Nat.eq_zero_or_pos A with hA | hA
    · rw [hA] at h3; omega
    · exact hA
  · rintro ⟨A, hA, h1, h2⟩
    -- n = x (m+1) + y (m-1) + z m with x + y + z = A
    obtain ⟨x, y, z, hxyz, hsum⟩ : ∃ x y z, x + y + z = A ∧
        x * (c + 4) + y * (c + 2) + z * (c + 3) = n := by
      rcases Nat.le_total (A * (c + 3)) n with hle | hle
      · refine ⟨n - A * (c + 3), 0, A - (n - A * (c + 3)), ?_, ?_⟩
        · have : n - A * (c + 3) ≤ A := by
            have : A * (c + 4) = A * (c + 3) + A := by ring
            omega
          omega
        · have hx : n - A * (c + 3) ≤ A := by
            have : A * (c + 4) = A * (c + 3) + A := by ring
            omega
          obtain ⟨x, hx'⟩ : ∃ x, x = n - A * (c + 3) := ⟨_, rfl⟩
          rw [← hx'] at hx ⊢
          obtain ⟨z, rfl⟩ : ∃ z, A = x + z := ⟨A - x, by omega⟩
          rw [Nat.add_sub_cancel_left]
          have e : x * (c + 4) + 0 * (c + 2) + z * (c + 3) = (x + z) * (c + 3) + x := by ring
          omega
      · refine ⟨0, A * (c + 3) - n, A - (A * (c + 3) - n), ?_, ?_⟩
        · have : A * (c + 2) + A = A * (c + 3) := by ring
          omega
        · have hy : A * (c + 3) - n ≤ A := by
            have : A * (c + 2) + A = A * (c + 3) := by ring
            omega
          obtain ⟨y, hy'⟩ : ∃ y, y = A * (c + 3) - n := ⟨_, rfl⟩
          rw [← hy'] at hy ⊢
          obtain ⟨z, rfl⟩ : ∃ z, A = y + z := ⟨A - y, by omega⟩
          rw [Nat.add_sub_cancel_left]
          have e : 0 * (c + 4) + y * (c + 2) + z * (c + 3) + y = (y + z) * (c + 3) := by ring
          omega
    let s : Multiset ℕ := Multiset.replicate x (c + 4) + Multiset.replicate y (c + 2) +
      Multiset.replicate z (c + 3)
    have hmem : ∀ q ∈ s, q = c + 4 ∨ q = c + 2 ∨ q = c + 3 := by
      intro q hq
      simp only [s, Multiset.mem_add, Multiset.mem_replicate] at hq
      omega
    let p : n.Partition :=
      { parts := s
        parts_pos := fun {i} hi => by rcases hmem i hi with h | h | h <;> omega
        parts_sum := by simp [s, ← hsum] }
    apply Finset.card_pos.mpr
    refine ⟨p, ?_⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨?_, ?_⟩
    · intro i hi
      rcases hmem i hi with h | h | h <;> rw [h] <;> unfold good
      · right; left
        rw [show c + 4 = (c + 3) + 1 by omega, Nat.add_mod_left]
        exact Nat.mod_eq_of_lt (by omega)
      · right; right
        rw [Nat.mod_eq_of_lt (by omega)]; omega
      · left; exact Nat.mod_self _
    · intro h1
      rcases hmem 1 h1 with h | h | h <;> omega

/-- Column k = c + 1 (m = k + 2 = c + 3): T(n+1) = T(n) exactly when
A(m+1) ≤ n ≤ (A+1)(m-1) - 2 for some A ≥ 0.  So the plateaus (maximal runs of equal terms) are
n ∈ [A(m+1), (A+1)(m-1) - 1], of length m - 1 - 2A = k + 1 - 2A, for every A with k + 1 - 2A ≥ 2,
and the column is strictly increasing elsewhere. -/
theorem flat_iff (c n : ℕ) :
    T (c + 3) (n + 1) = T (c + 3) n ↔ ∃ A, A * (c + 4) ≤ n ∧ n + 2 ≤ (A + 1) * (c + 2) := by
  rw [T_succ (c + 3) n (by omega)]
  have hD := D_pos_iff c (n + 1) (by omega)
  constructor
  · intro h
    have h0 : D (c + 3) (n + 1) = 0 := by omega
    have hno : ¬ ∃ A, 1 ≤ A ∧ A * (c + 2) ≤ n + 1 ∧ n + 1 ≤ A * (c + 4) := by
      rw [← hD]; omega
    have hle := Nat.div_mul_le_self n (c + 4)
    have hdm := Nat.div_add_mod n (c + 4)
    have hmod := Nat.mod_lt n (show 0 < c + 4 by omega)
    obtain ⟨q, hq⟩ : ∃ q, q = n / (c + 4) := ⟨_, rfl⟩
    rw [← hq] at hle hdm
    refine ⟨q, hle, ?_⟩
    have hlt : n < (q + 1) * (c + 4) := by nlinarith
    by_contra hc
    exact hno ⟨q + 1, by omega, by omega, by omega⟩
  · rintro ⟨A0, h1, h2⟩
    have hno : ¬ 0 < D (c + 3) (n + 1) := by
      rw [hD]
      rintro ⟨A, hA, h3, h4⟩
      rcases Nat.le_total A A0 with hle | hle
      · have := Nat.mul_le_mul_right (c + 4) hle
        omega
      · have hle' : A0 + 1 ≤ A ∨ A = A0 := by omega
        rcases hle' with hle' | rfl
        · have := Nat.mul_le_mul_right (c + 2) hle'
          omega
        · omega
    omega

/-! ### Levels: T_m(A(m+1)) does not depend on m once m ≥ 2A + 3 -/

theorem decomp (d q : ℕ) (hd : 3 ≤ d) (hq : good d q) (h2 : 2 ≤ q) :
    ∃ a e, 1 ≤ a ∧ e ≤ 2 ∧ q + 1 = a * d + e := by
  have hdm := Nat.div_add_mod q d
  obtain ⟨t, ht⟩ : ∃ t, t = q / d := ⟨_, rfl⟩
  rw [← ht] at hdm
  rcases hq with h | h | h
  · rw [h] at hdm
    refine ⟨t, 1, ?_, by omega, by rw [← hdm]; ring⟩
    rcases Nat.eq_zero_or_pos t with h0 | h0
    · rw [h0] at hdm; omega
    · exact h0
  · rw [h] at hdm
    refine ⟨t, 2, ?_, by omega, by rw [← hdm]; ring⟩
    rcases Nat.eq_zero_or_pos t with h0 | h0
    · rw [h0] at hdm; omega
    · exact h0
  · rw [h] at hdm
    refine ⟨t + 1, 0, by omega, by omega, ?_⟩
    have : d * t + (d - 1) + 1 = (t + 1) * d := by
      have : d - 1 + 1 = d := by omega
      rw [Nat.add_assoc, this]; ring
    omega

theorem recomp (d q a e : ℕ) (hd : 3 ≤ d) (ha : 1 ≤ a) (he : e ≤ 2) (h : q + 1 = a * d + e) :
    good d q ∧ 2 ≤ q ∧ (q + 1) / d = a := by
  have had : d ≤ a * d := Nat.le_mul_of_pos_left d ha
  refine ⟨?_, by omega, ?_⟩
  · unfold good
    obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
    rcases (show e = 0 ∨ e = 1 ∨ e = 2 by omega) with rfl | rfl | rfl
    · right; right
      have : q = (d - 1) + d * b := by
        have : (b + 1) * d = d * b + d := by ring
        omega
      rw [this, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
    · left
      have : q = d * (b + 1) := by
        have : (b + 1) * d = d * (b + 1) := by ring
        omega
      rw [this, Nat.mul_mod_right]
    · right; left
      have : q = 1 + d * (b + 1) := by
        have : (b + 1) * d = d * (b + 1) := by ring
        omega
      rw [this, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
  · rw [h, Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt (by omega)]
    omega

/-- q = a d + e - 1 ↦ a (d+1) + e - 1. -/
def up (d q : ℕ) : ℕ := q + (q + 1) / d
/-- inverse of `up`. -/
def down (d q : ℕ) : ℕ := q - (q + 1) / (d + 1)

theorem up_spec (d q : ℕ) (hd : 3 ≤ d) (hq : good d q) (h2 : 2 ≤ q) :
    good (d + 1) (up d q) ∧ 2 ≤ up d q ∧ down d (up d q) = q ∧ (q + 1) / d * (d - 1) ≤ q := by
  obtain ⟨a, e, ha, he, h⟩ := decomp d q hd hq h2
  have h1 := (recomp d q a e hd ha he h).2.2
  have hu : up d q + 1 = a * (d + 1) + e := by unfold up; rw [h1]; nlinarith
  have h3 := recomp (d + 1) (up d q) a e (by omega) ha he hu
  refine ⟨h3.1, h3.2.1, ?_, ?_⟩
  · unfold down; rw [h3.2.2]; unfold up; rw [h1]; omega
  · rw [h1]
    have : a * (d - 1) + a = a * d := by
      rw [← Nat.mul_add_one, Nat.sub_add_cancel (by omega)]
    omega

theorem down_spec (d q : ℕ) (hd : 3 ≤ d) (hq : good (d + 1) q) (h2 : 2 ≤ q) :
    good d (down d q) ∧ 2 ≤ down d q ∧ up d (down d q) = q ∧ (q + 1) / (d + 1) * d ≤ q := by
  obtain ⟨a, e, ha, he, h⟩ := decomp (d + 1) q (by omega) hq h2
  have h1 := (recomp (d + 1) q a e (by omega) ha he h).2.2
  have hdn : down d q + 1 = a * d + e := by
    unfold down; rw [h1]
    have : a ≤ q := by nlinarith
    have : a * (d + 1) = a * d + a := by ring
    omega
  have h3 := recomp d (down d q) a e hd ha he hdn
  refine ⟨h3.1, h3.2.1, ?_, ?_⟩
  · unfold up; rw [h3.2.2]; unfold down; rw [h1]
    have : a ≤ q := by nlinarith
    omega
  · rw [h1]
    have : a * (d + 1) = a * d + a := by ring
    omega

theorem sum_weights (s : Multiset ℕ) (w : ℕ → ℕ) (k : ℕ) (hs : ∀ q ∈ s, w q * k ≤ q) :
    (s.map w).sum * k ≤ s.sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons q s ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons, add_mul]
    have := hs q (Multiset.mem_cons_self q s)
    have := ih (fun x hx => hs x (Multiset.mem_cons_of_mem hx))
    omega

theorem sum_weights_upper (s : Multiset ℕ) (w : ℕ → ℕ) (k : ℕ) (hs : ∀ q ∈ s, q ≤ w q * k) :
    s.sum ≤ (s.map w).sum * k := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons q s ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons, add_mul]
    have := hs q (Multiset.mem_cons_self q s)
    have := ih (fun x hx => hs x (Multiset.mem_cons_of_mem hx))
    omega

theorem sum_up (d : ℕ) (s : Multiset ℕ) :
    (s.map (up d)).sum = s.sum + (s.map (fun q => (q + 1) / d)).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons q s ih => simp only [Multiset.map_cons, Multiset.sum_cons, ih, up]; ring

theorem sum_down (d : ℕ) (s : Multiset ℕ) (hs : ∀ q ∈ s, (q + 1) / (d + 1) ≤ q) :
    (s.map (down d)).sum + (s.map (fun q => (q + 1) / (d + 1))).sum = s.sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons q s ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons, down]
    have := hs q (Multiset.mem_cons_self q s)
    have := ih (fun x hx => hs x (Multiset.mem_cons_of_mem hx))
    omega

/-- Non-1 parts of a partition and the number of 1s. -/
theorem parts_split {n : ℕ} (p : n.Partition) :
    p.parts = p.parts.filter (· ≠ 1) + Multiset.replicate (p.parts.count 1) 1 := by
  rw [← Multiset.filter_eq' p.parts 1, add_comm]
  have := Multiset.filter_add_not (fun x => x = 1) p.parts
  simpa using this.symm

theorem sum_split {n : ℕ} (p : n.Partition) : (p.parts.filter (· ≠ 1)).sum + p.parts.count 1 = n := by
  have h := congrArg Multiset.sum (parts_split p)
  rw [p.parts_sum, Multiset.sum_add, Multiset.sum_replicate, smul_eq_mul, mul_one] at h
  exact h.symm

theorem filter_build (t : Multiset ℕ) (k : ℕ) (ht : ∀ x ∈ t, 2 ≤ x) :
    (t + Multiset.replicate k 1).filter (· ≠ 1) = t := by
  rw [Multiset.filter_add, Multiset.filter_eq_self.mpr (fun x hx => by have := ht x hx; omega)]
  rw [Multiset.filter_eq_nil.mpr (fun x hx => by rw [Multiset.eq_of_mem_replicate hx]; simp)]
  simp

theorem nonone_spec {n : ℕ} (p : n.Partition) (d : ℕ) (hp : ∀ i ∈ p.parts, good d i) :
    ∀ q ∈ p.parts.filter (· ≠ 1), good d q ∧ 2 ≤ q := by
  intro q hq
  rw [Multiset.mem_filter] at hq
  have := p.parts_pos hq.1
  exact ⟨hp q hq.1, by omega⟩

/-- The map on good partitions of A(d+1) (parts ≡ 0, ±1 mod d) to those of A(d+2) (mod d+1). -/
def Φ (d A : ℕ) (hd : 2 * A + 3 ≤ d) (p : (A * (d + 1)).Partition)
    (hp : ∀ i ∈ p.parts, good d i) : (A * (d + 2)).Partition where
  parts := (p.parts.filter (· ≠ 1)).map (up d) +
    Multiset.replicate (A * (d + 2) - ((p.parts.filter (· ≠ 1)).map (up d)).sum) 1
  parts_pos := by
    intro i hi
    rcases Multiset.mem_add.mp hi with h | h
    · obtain ⟨q, hq, rfl⟩ := Multiset.mem_map.mp h
      have := (up_spec d q (by omega) (nonone_spec p d hp q hq).1 (nonone_spec p d hp q hq).2).2.1
      omega
    · rw [Multiset.eq_of_mem_replicate h]; omega
  parts_sum := by
    have hs := sum_split p
    have hw := sum_weights (p.parts.filter (· ≠ 1)) (fun q => (q + 1) / d) (d - 1) (fun q hq =>
      (up_spec d q (by omega) (nonone_spec p d hp q hq).1 (nonone_spec p d hp q hq).2).2.2.2)
    have hu := sum_up d (p.parts.filter (· ≠ 1))
    generalize (p.parts.filter (· ≠ 1)).sum = S at hs hw hu
    generalize ((p.parts.filter (· ≠ 1)).map (fun q => (q + 1) / d)).sum = W at hw hu
    obtain ⟨x, rfl⟩ : ∃ x, d = x + 1 := ⟨d - 1, by omega⟩
    simp only [Nat.add_sub_cancel] at hw
    have hWA : W ≤ A := by
      by_contra hc
      have h1 : (A + 1) * x ≤ W * x := Nat.mul_le_mul_right _ (by omega)
      have e1 : A * (x + 1 + 1) = A * x + 2 * A := by ring
      have e2 : (A + 1) * x = A * x + x := by ring
      omega
    rw [Multiset.sum_add, Multiset.sum_replicate, smul_eq_mul, mul_one, hu]
    have e3 : A * (x + 1 + 2) = A * (x + 1 + 1) + A := by ring
    omega

/-- The inverse map. -/
def Ψ (d A : ℕ) (hd : 2 * A + 3 ≤ d) (p : (A * (d + 2)).Partition)
    (hp : ∀ i ∈ p.parts, good (d + 1) i) : (A * (d + 1)).Partition where
  parts := (p.parts.filter (· ≠ 1)).map (down d) +
    Multiset.replicate (A * (d + 1) - ((p.parts.filter (· ≠ 1)).map (down d)).sum) 1
  parts_pos := by
    intro i hi
    rcases Multiset.mem_add.mp hi with h | h
    · obtain ⟨q, hq, rfl⟩ := Multiset.mem_map.mp h
      have := (down_spec d q (by omega) (nonone_spec p (d + 1) hp q hq).1
        (nonone_spec p (d + 1) hp q hq).2).2.1
      omega
    · rw [Multiset.eq_of_mem_replicate h]; omega
  parts_sum := by
    have hs := sum_split p
    have spec := fun q (hq : q ∈ p.parts.filter (· ≠ 1)) =>
      down_spec d q (by omega) (nonone_spec p (d + 1) hp q hq).1 (nonone_spec p (d + 1) hp q hq).2
    have hw := sum_weights (p.parts.filter (· ≠ 1)) (fun q => (q + 1) / (d + 1)) d
      (fun q hq => (spec q hq).2.2.2)
    have hdn := sum_down d (p.parts.filter (· ≠ 1)) (fun q hq => by
      have := (spec q hq).2.2.2
      have : (q + 1) / (d + 1) ≤ (q + 1) / (d + 1) * d := Nat.le_mul_of_pos_right _ (by omega)
      omega)
    have hupper := sum_weights_upper (p.parts.filter (· ≠ 1)) (fun q => (q + 1) / (d + 1)) (d + 2)
      (fun q hq => by
        obtain ⟨a, e, ha, he, h⟩ := decomp (d + 1) q (by omega) (nonone_spec p (d + 1) hp q hq).1
          (nonone_spec p (d + 1) hp q hq).2
        show q ≤ (q + 1) / (d + 1) * (d + 2)
        rw [(recomp (d + 1) q a e (by omega) ha he h).2.2]
        nlinarith)
    generalize (p.parts.filter (· ≠ 1)).sum = S at hs hw hdn hupper
    generalize ((p.parts.filter (· ≠ 1)).map (fun q => (q + 1) / (d + 1))).sum = W at hw hdn hupper
    have hWA : W ≤ A := by
      by_contra hc
      have h1 : (A + 1) * d ≤ W * d := Nat.mul_le_mul_right _ (by omega)
      have e1 : A * (d + 2) = A * d + 2 * A := by ring
      have e2 : (A + 1) * d = A * d + d := by ring
      omega
    rw [Multiset.sum_add, Multiset.sum_replicate, smul_eq_mul, mul_one]
    have h3 : W * (d + 2) = W * (d + 1) + W := by ring
    have h4 : W * (d + 1) ≤ A * (d + 1) := Nat.mul_le_mul_right _ hWA
    omega

theorem rebuild {n : ℕ} (p : n.Partition) :
    p.parts.filter (· ≠ 1) + Multiset.replicate (n - (p.parts.filter (· ≠ 1)).sum) 1 = p.parts := by
  have h1 := sum_split p
  conv_rhs => rw [parts_split p]
  congr 2
  omega

/-- The level of plateau A is the same in columns d - 2 and d - 1 (m = d and d + 1) when
2A + 3 ≤ d. -/
theorem level_step (d A : ℕ) (hd : 2 * A + 3 ≤ d) : T d (A * (d + 1)) = T (d + 1) (A * (d + 2)) := by
  unfold T
  apply Finset.card_bij' (fun p hp => Φ d A hd p (by simpa using hp))
    (fun p hp => Ψ d A hd p (by simpa using hp))
  case hi =>
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    intro i hi
    rcases Multiset.mem_add.mp hi with h | h
    · obtain ⟨q, hq, rfl⟩ := Multiset.mem_map.mp h
      exact (up_spec d q (by omega) (nonone_spec p d hp q hq).1 (nonone_spec p d hp q hq).2).1
    · rw [Multiset.eq_of_mem_replicate h]; exact good_one _ (by omega)

  case left_inv =>
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    apply Nat.Partition.ext
    show ((Φ d A hd p _).parts.filter (· ≠ 1)).map (down d) + _ = p.parts
    have hf : (Φ d A hd p (by simpa using hp)).parts.filter (· ≠ 1) =
        (p.parts.filter (· ≠ 1)).map (up d) := by
      apply filter_build
      intro x hx
      obtain ⟨q, hq, rfl⟩ := Multiset.mem_map.mp hx
      exact (up_spec d q (by omega) (nonone_spec p d hp q hq).1 (nonone_spec p d hp q hq).2).2.1
    have hm : ((p.parts.filter (· ≠ 1)).map (up d)).map (down d) = p.parts.filter (· ≠ 1) := by
      rw [Multiset.map_map]
      conv_rhs => rw [← Multiset.map_id (p.parts.filter (· ≠ 1))]
      apply Multiset.map_congr rfl
      intro q hq
      exact (up_spec d q (by omega) (nonone_spec p d hp q hq).1 (nonone_spec p d hp q hq).2).2.2.1
    rw [hf, hm]
    exact rebuild p

  case right_inv =>
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    apply Nat.Partition.ext
    show ((Ψ d A hd p _).parts.filter (· ≠ 1)).map (up d) + _ = p.parts
    have hf : (Ψ d A hd p (by simpa using hp)).parts.filter (· ≠ 1) =
        (p.parts.filter (· ≠ 1)).map (down d) := by
      apply filter_build
      intro x hx
      obtain ⟨q, hq, rfl⟩ := Multiset.mem_map.mp hx
      exact (down_spec d q (by omega) (nonone_spec p (d + 1) hp q hq).1
        (nonone_spec p (d + 1) hp q hq).2).2.1
    have hm : ((p.parts.filter (· ≠ 1)).map (down d)).map (up d) = p.parts.filter (· ≠ 1) := by
      rw [Multiset.map_map]
      conv_rhs => rw [← Multiset.map_id (p.parts.filter (· ≠ 1))]
      apply Multiset.map_congr rfl
      intro q hq
      exact (down_spec d q (by omega) (nonone_spec p (d + 1) hp q hq).1
        (nonone_spec p (d + 1) hp q hq).2).2.2.1
    rw [hf, hm]
    exact rebuild p

  case hj =>
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    intro i hi
    rcases Multiset.mem_add.mp hi with h | h
    · obtain ⟨q, hq, rfl⟩ := Multiset.mem_map.mp h
      exact (down_spec d q (by omega) (nonone_spec p (d + 1) hp q hq).1
        (nonone_spec p (d + 1) hp q hq).2).1
    · rw [Multiset.eq_of_mem_replicate h]; exact good_one _ (by omega)

/-- Level of plateau A in column k (m = k + 2): T_m(A(m+1)) is the same for all k ≥ 2A + 1,
so it equals its limit as k → ∞, which is A210843(A+1) by that entry's definition. -/
theorem level_const (A k : ℕ) (hk : 2 * A + 1 ≤ k) :
    T (k + 2) (A * (k + 3)) = T (2 * A + 3) (A * (2 * A + 4)) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = 2 * A + 1 + j := ⟨k - (2 * A + 1), by omega⟩
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [← ih (by omega)]
    have := level_step (2 * A + 1 + j + 2) A (by omega)
    rw [show 2 * A + 1 + (j + 1) + 2 = 2 * A + 1 + j + 2 + 1 by omega,
      show 2 * A + 1 + (j + 1) + 3 = 2 * A + 1 + j + 2 + 2 by omega,
      show 2 * A + 1 + j + 3 = 2 * A + 1 + j + 2 + 1 by omega]
    exact this.symm

end OEIS_A195825

open OEIS_A195825
