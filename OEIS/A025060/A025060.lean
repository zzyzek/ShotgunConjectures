/-
OEIS A025060 (numbers i*j + j*k + k*i with 1 ≤ i < j < k).  Conjecture
(J. Perry, 2013): if i, j, k may be negative but nonzero and still distinct,
every integer occurs.  True (trivial).

Checked here (core Lean, full statement):
* `main`: every integer v equals i*j + j*k + k*i for some distinct nonzero
  integers i, j, k.  For v ∉ {-3, -2, 0} take (2, -1, v + 2), which gives
  -2 + (v + 2)(2 - 1) = v; for v ∈ {-3, -2, 0} take (4, -3, v + 12), which
  gives -12 + (v + 12) = v.
Not checked here: nothing.
-/

def Rep (v : Int) : Prop :=
  ∃ i j k : Int, i ≠ 0 ∧ j ≠ 0 ∧ k ≠ 0 ∧ i ≠ j ∧ j ≠ k ∧ i ≠ k ∧ i * j + j * k + k * i = v

theorem main (v : Int) : Rep v := by
  by_cases h : v = -3 ∨ v = -2 ∨ v = 0
  · refine ⟨4, -3, v + 12, by decide, by decide, by omega, by decide, by omega, by omega, ?_⟩
    omega
  · refine ⟨2, -1, v + 2, by decide, by decide, by omega, by decide, by omega, by omega, ?_⟩
    omega
