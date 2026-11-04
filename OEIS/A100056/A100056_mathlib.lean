/-
OEIS A100056, Mathlib proof.

A100056(n): sum of the absolute values of the consecutive differences of
the A054065 permutation of 1..n; A054065 orders h = 1..n by the fractional
part of h·φ (φ the golden ratio), increasing. Conjecture: a(n) is the
maximum of Σ |π(i+1) - π(i)| over all permutations π of 1..n.

Definitions: `A100056_IsRow n p`: p is a permutation of [1, ..., n] along
which Int.fract (h·φ) strictly increases (the A054065 row, with φ =
`goldenRatio`); `A100056_sumDiff p` = Σ |p(i+1) - p(i)|.

Main theorem `A100056_main`: [5, 2, 4, 1, 3] is the A054065 row for n = 5
and the only list with that property, its sum is 10, while [4, 2, 5, 1, 3]
is a permutation of 1..5 with sum 11. So a(5) = 10 is not the maximum and
the conjecture fails at n = 5, the README result. (The maxima for n ≤ 9
listed in the README come from the certificate script and are not part of
the disproof.) Nothing is outside Lean.
-/
import Mathlib

open Real

/-- p is the A054065 row for n: a permutation of 1..n ordered by fract(h φ). -/
def A100056_IsRow (n : ℕ) (p : List ℕ) : Prop :=
  p.Perm (List.range' 1 n) ∧
    p.Pairwise (fun a b : ℕ => Int.fract ((a : ℝ) * goldenRatio) < Int.fract ((b : ℝ) * goldenRatio))

/-- Σ |p(i+1) - p(i)| over consecutive entries. -/
def A100056_sumDiff : List ℕ → ℤ
  | a :: b :: l => |(b : ℤ) - a| + A100056_sumDiff (b :: l)
  | _ => 0

theorem A100056_fract (h : ℕ) (k : ℤ) (lo hi : ℝ) (hpos : 0 < h)
    (hφ1 : (1.6180339 : ℝ) < goldenRatio) (hφ2 : goldenRatio < 1.618034)
    (hlo : 0 ≤ (h : ℝ) * 1.6180339 - k) (hhi : (h : ℝ) * 1.618034 - k < 1)
    (hl : lo ≤ (h : ℝ) * 1.6180339 - k) (hh : (h : ℝ) * 1.618034 - k ≤ hi) :
    lo < Int.fract ((h : ℝ) * goldenRatio) ∧ Int.fract ((h : ℝ) * goldenRatio) < hi := by
  have hp : (0 : ℝ) < h := by exact_mod_cast hpos
  have e : Int.fract ((h : ℝ) * goldenRatio) = (h : ℝ) * goldenRatio - k := by
    rw [Int.fract_eq_iff]
    refine ⟨by nlinarith, by nlinarith, ⟨k, by ring⟩⟩
  rw [e]
  constructor <;> nlinarith

theorem A100056_main :
    A100056_IsRow 5 [5, 2, 4, 1, 3] ∧
    (∀ p, A100056_IsRow 5 p → p = [5, 2, 4, 1, 3]) ∧
    A100056_sumDiff [5, 2, 4, 1, 3] = 10 ∧
    [4, 2, 5, 1, 3].Perm (List.range' 1 5) ∧ A100056_sumDiff [4, 2, 5, 1, 3] = 11 := by
  have s5 : (2.2360678 : ℝ) < √5 := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  have s5' : √5 < 2.236068 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have hφ1 : (1.6180339 : ℝ) < goldenRatio := by rw [goldenRatio]; linarith
  have hφ2 : goldenRatio < 1.618034 := by rw [goldenRatio]; linarith
  obtain ⟨f1l, f1h⟩ := A100056_fract 1 1 0.61 0.62 (by norm_num) hφ1 hφ2 (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨f2l, f2h⟩ := A100056_fract 2 3 0.23 0.24 (by norm_num) hφ1 hφ2 (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨f3l, f3h⟩ := A100056_fract 3 4 0.85 0.86 (by norm_num) hφ1 hφ2 (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨f4l, f4h⟩ := A100056_fract 4 6 0.47 0.48 (by norm_num) hφ1 hφ2 (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨f5l, f5h⟩ := A100056_fract 5 8 0.08 0.10 (by norm_num) hφ1 hφ2 (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  have hrow : A100056_IsRow 5 [5, 2, 4, 1, 3] := by
    refine ⟨by decide, ?_⟩
    simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil,
      or_false, forall_eq_or_imp, forall_eq, List.Pairwise.nil, and_true, IsEmpty.forall_iff,
      implies_true]
    simp only [Nat.cast_ofNat, Nat.cast_one] at *
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩ <;> linarith
  refine ⟨hrow, fun p hp => ?_, by decide, by decide, by decide⟩
  refine List.Perm.eq_of_pairwise (le := fun a b : ℕ =>
    Int.fract ((a : ℝ) * goldenRatio) < Int.fract ((b : ℝ) * goldenRatio)) ?_ hp.2 hrow.2
    (hp.1.trans hrow.1.symm)
  exact fun _ _ _ _ hab hba => absurd (hab.trans hba) (lt_irrefl _)
