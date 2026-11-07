/-
AMR froberg-O (Froberg-Lundqvist-Oneto-Shapiro 2018, Problem O): periods of
phi(f) = sum over zeros a of f in F_p of x^a, n = 1.
After one step every state is a 0/1 polynomial, i.e. a set S of exponents in {0, ..., p-1};
`phiL p S` lists the zeros b in {0, ..., p-1} of sum_{a in S} x^a (with 0^0 = 1, the value of the
constant monomial), which is the exponent set of the next state.
Checked here (kernel evaluation): the cycles found by the search in certificate/:
2-cycles at p = 71 (the paper's), 127, 151, a 4-cycle at p = 541 that is not the standard
4-cycle 0 -> F_p -> {1} -> {0} -> 0, and a cycle of exact period 6 at p = 1009
(`cycle1009`: the six states map to each other in order;
`period_six_1009`: they are pairwise distinct, so the period is exactly 6). Also `zero_alternates`: 0 is a zero of sum_{a in S} x^a
iff 0 is not in S (for S without repetitions), which makes every period even.
Not checked here: the exhaustive census for p <= 31 and the small-support search (C programs).
-/

def phiL (p : Nat) (S : List Nat) : List Nat :=
  (List.range p).filter (fun b => (S.map (fun a => b ^ a)).sum % p == 0)

theorem cycle71 : phiL 71 [23, 26, 34, 39, 41, 51, 70] = [0, 63] ∧
    phiL 71 [0, 63] = [23, 26, 34, 39, 41, 51, 70] := by decide +kernel

theorem cycle127 : phiL 127 [38, 89] = [0, 20, 108, 126] ∧
    phiL 127 [0, 20, 108, 126] = [38, 89] := by decide +kernel

theorem cycle151 : phiL 151 [69, 150] = [0, 33, 119, 150] ∧
    phiL 151 [0, 33, 119, 150] = [69, 150] := by decide +kernel

theorem cycle541 : phiL 541 [129, 411] = [0, 52, 216, 268, 273, 325, 489] ∧
    phiL 541 [0, 52, 216, 268, 273, 325, 489] = [120, 133, 529] ∧
    phiL 541 [120, 133, 529] = [0, 163, 362] ∧
    phiL 541 [0, 163, 362] = [129, 411] := by decide +kernel

theorem cycle1009 : phiL 1009 [472, 553, 786, 868] = [0, 121, 144] ∧
    phiL 1009 [0, 121, 144] = [446, 495] ∧
    phiL 1009 [446, 495] = [0, 74, 150, 578, 615, 707, 904, 1008] ∧
    phiL 1009 [0, 74, 150, 578, 615, 707, 904, 1008] = [103, 322, 775] ∧
    phiL 1009 [103, 322, 775] = [0, 337, 506, 561, 759, 922, 951] ∧
    phiL 1009 [0, 337, 506, 561, 759, 922, 951] = [472, 553, 786, 868] := by decide +kernel

theorem period_six_1009 : [[472, 553, 786, 868], [0, 121, 144], [446, 495],
    [0, 74, 150, 578, 615, 707, 904, 1008], [103, 322, 775],
    [0, 337, 506, 561, 759, 922, 951]].Nodup := by decide

theorem zero_pow_sum (S : List Nat) (h : S.Nodup) :
    (S.map (fun a => (0 : Nat) ^ a)).sum = if 0 ∈ S then 1 else 0 := by
  induction S with
  | nil => simp
  | cons x xs ih =>
    have hx : x ∉ xs := (List.nodup_cons.mp h).1
    have hxs : xs.Nodup := (List.nodup_cons.mp h).2
    rw [List.map_cons, List.sum_cons, ih hxs]
    by_cases h0 : x = 0
    · subst h0
      simp [hx]
    · have : (0 : Nat) ^ x = 0 := Nat.zero_pow (Nat.pos_of_ne_zero h0)
      rw [this]
      by_cases hm : 0 ∈ xs
      · simp [hm]
      · simp [hm]
        exact fun e => h0 e.symm

theorem zero_alternates (p : Nat) (hp : 2 ≤ p) (S : List Nat) (h : S.Nodup) :
    (0 ∈ phiL p S) ↔ (0 ∉ S) := by
  unfold phiL
  rw [List.mem_filter, zero_pow_sum S h]
  constructor
  · intro ⟨_, h2⟩ hm
    simp [hm] at h2
    omega
  · intro hm
    refine ⟨List.mem_range.mpr (by omega), ?_⟩
    simp [hm]
