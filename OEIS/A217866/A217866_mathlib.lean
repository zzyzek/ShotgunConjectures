import Mathlib

/-
OEIS A217866 and A217976 (both about A217865).
A050504(n) = floor(n log n); A217865(n) = A050504(n+1) - A050504(n), the first
differences (JavaScript program in A217865: floor((i+1) log(i+1)) - floor(i log i)).
A217866(v) = last index where v occurs in A217865, A217976(v) = first index.
Conjecture (both entries): the last time v appears is before the first time v+2 appears.

Definitions.  `A050504 n = ⌊n * Real.log n⌋` (an integer; `Real.log 0 = 0`),
`A217865 n = A050504 (n+1) - A050504 n`.

Main theorem.
* `A217866_conjecture`: if A217865 m = v and A217865 n = v + 2 then m < n.
  So every occurrence of v precedes every occurrence of v + 2; in particular
  A217866(v) < A217976(v+2) whenever both exist.

Route.
* `g n = (n+1) log(n+1) - n log n` is strictly increasing (`g_strictMono`), from
  strict convexity of x log x on [0, ∞) (`strictConvexOn_mul_log`) and
  `StrictConvexOn.slope_strict_mono_adjacent`.
* `A217865 n - g n` lies in (-1, 1) (`diff_close`), from the floor bounds.
* A217865 m = v forces g m < v + 1; A217865 n = v + 2 forces g n > v + 1.

Not checked here: agreement of these definitions with the listed OEIS terms
(certificate/check.py recomputes them with floating point).
-/

open Real

noncomputable def A050504 (n : ℕ) : ℤ := ⌊(n : ℝ) * Real.log n⌋

noncomputable def A217865 (n : ℕ) : ℤ := A050504 (n + 1) - A050504 n

noncomputable def g (n : ℕ) : ℝ :=
  ((n : ℝ) + 1) * Real.log ((n : ℝ) + 1) - (n : ℝ) * Real.log n

theorem g_lt_succ (n : ℕ) : g n < g (n + 1) := by
  have h := strictConvexOn_mul_log.slope_strict_mono_adjacent
    (x := (n : ℝ)) (y := (n : ℝ) + 1) (z := (n : ℝ) + 2)
    (by simp [Set.mem_Ici]) (by simp [Set.mem_Ici]; positivity)
    (by linarith) (by linarith)
  have e1 : ((n : ℝ) + 1) - n = 1 := by ring
  have e2 : ((n : ℝ) + 2) - ((n : ℝ) + 1) = 1 := by ring
  rw [e1, e2, div_one, div_one] at h
  unfold g
  push_cast
  have e3 : ((n : ℝ) + 1 + 1) = (n : ℝ) + 2 := by ring
  rw [e3]
  linarith

theorem g_strictMono : StrictMono g := strictMono_nat_of_lt_succ g_lt_succ

theorem diff_close (n : ℕ) :
    (A217865 n : ℝ) < g n + 1 ∧ g n - 1 < (A217865 n : ℝ) := by
  unfold A217865 A050504 g
  have a1 := Int.floor_le (((n + 1 : ℕ) : ℝ) * Real.log ((n + 1 : ℕ) : ℝ))
  have a2 := Int.lt_floor_add_one (((n + 1 : ℕ) : ℝ) * Real.log ((n + 1 : ℕ) : ℝ))
  have b1 := Int.floor_le ((n : ℝ) * Real.log (n : ℝ))
  have b2 := Int.lt_floor_add_one ((n : ℝ) * Real.log (n : ℝ))
  push_cast at *
  constructor <;> linarith

theorem A217866_conjecture (m n : ℕ) (v : ℤ)
    (hm : A217865 m = v) (hn : A217865 n = v + 2) : m < n := by
  have h1 := (diff_close m).2
  have h2 := (diff_close n).1
  rw [hm] at h1
  rw [hn] at h2
  push_cast at h2
  have hlt : g m < g n := by linarith
  exact g_strictMono.lt_iff_lt.mp hlt
