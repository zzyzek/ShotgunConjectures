import Mathlib

/-
Guy, UPINT E22 (Gupta): m(n) is the least length of a cycle a_1, ..., a_m with entries in
[1, n] such that every permutation of 1..n is a (not necessarily consecutive) subsequence of
a_j, ..., a_m, a_1, ..., a_{j-1} for some j. Gupta conjectured m(n) ≤ ⌊n²/2⌋; proved for even n
by Lecouturier and Zmiaikou (2012); open for odd n. OEIS A373728 lists m(n) for n ≤ 6.

Checked here (`rosary7`): the cycle W of length 24 = ⌊7²/2⌋ below contains every permutation
of [1, 7] in some rotation, so m(7) ≤ 24 and Gupta's bound holds for n = 7. The 5040
permutations are checked by the kernel (`decide`) with a Boolean subsequence test whose
soundness is proved (`isSubseq_sound`).
Not checked here: whether m(7) < 24.
-/

namespace NT_E22_1

def isSubseq : List Nat → List Nat → Bool
  | [], _ => true
  | _ :: _, [] => false
  | x :: xs, y :: ys => if x = y then isSubseq xs ys else isSubseq (x :: xs) ys

theorem isSubseq_sound : ∀ (p s : List Nat), isSubseq p s = true → p.Sublist s
  | [], s, _ => List.nil_sublist s
  | _ :: _, [], h => by simp [isSubseq] at h
  | x :: xs, y :: ys, h => by
    unfold isSubseq at h
    split at h
    · rename_i hxy; subst hxy; exact (isSubseq_sound xs ys h).cons_cons x
    · exact (isSubseq_sound (x :: xs) ys h).cons y

/-- Rotation starting at position j. -/
def rot (w : List Nat) (j : Nat) : List Nat := w.drop j ++ w.take j

def covers (w p : List Nat) : Bool := (List.range w.length).any (fun j => isSubseq p (rot w j))

/-- All insertions of x into a list. -/
def insertAll (x : Nat) : List Nat → List (List Nat)
  | [] => [[x]]
  | y :: ys => (x :: y :: ys) :: (insertAll x ys).map (y :: ·)

/-- All permutations, by structural recursion (kernel-reducible). -/
def perms : List Nat → List (List Nat)
  | [] => [[]]
  | x :: xs => (perms xs).flatMap (insertAll x)

theorem mem_insertAll (x : Nat) : ∀ (l1 l2 : List Nat), l1 ++ x :: l2 ∈ insertAll x (l1 ++ l2)
  | [], [] => by simp [insertAll]
  | [], y :: ys => by simp [insertAll]
  | y :: ys, l2 => by
    simp only [List.cons_append, insertAll, List.mem_cons, List.mem_map]
    exact Or.inr ⟨ys ++ x :: l2, mem_insertAll x ys l2, rfl⟩

theorem mem_perms : ∀ (l p : List Nat), p.Perm l → p ∈ perms l
  | [], p, h => by simp [List.Perm.eq_nil h, perms]
  | x :: xs, p, h => by
    have hx : x ∈ p := h.symm.subset (List.mem_cons_self ..)
    obtain ⟨l1, l2, rfl⟩ := List.append_of_mem hx
    have h' : (l1 ++ l2).Perm xs := (List.perm_middle.symm.trans h).cons_inv
    simp only [perms, List.mem_flatMap]
    exact ⟨l1 ++ l2, mem_perms xs _ h', mem_insertAll x l1 l2⟩

def W : List Nat := [2, 5, 1, 6, 7, 3, 5, 1, 2, 4, 7, 6, 1, 5, 3, 7, 4, 2, 1, 5, 6, 7, 3, 4]

theorem W_length : W.length = 24 := rfl

theorem W_entries : ∀ a ∈ W, 1 ≤ a ∧ a ≤ 7 := by decide

theorem all_covered : (perms [1, 2, 3, 4, 5, 6, 7]).all (covers W) = true := by
  decide +kernel

/-- Every permutation p of 1..7 is a subsequence of some rotation of W (|W| = 24 = ⌊49/2⌋). -/
theorem rosary7 (p : List Nat) (hp : p.Perm [1, 2, 3, 4, 5, 6, 7]) :
    ∃ j, j < W.length ∧ p.Sublist (rot W j) := by
  have hm : p ∈ perms [1, 2, 3, 4, 5, 6, 7] := mem_perms _ p hp
  have h := List.all_eq_true.1 all_covered p hm
  unfold covers at h
  obtain ⟨j, hj, hs⟩ := List.any_eq_true.1 h
  exact ⟨j, List.mem_range.1 hj, isSubseq_sound _ _ hs⟩
