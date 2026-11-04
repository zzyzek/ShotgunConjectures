/-
OEIS A133212, Mathlib proof.

A133212: a(0..3) = 1, 4, 12, 32 and a(n) = 4a(n-1) - 6a(n-2) + 4a(n-3) for
n > 3. A038503(m) = Σ_k C(m, 4k). Conjecture (R. J. Mathar, 2007):
a(n) = 2·A038503(n+3) for n > 0.

Main theorem `A133212_main`: for every n ≥ 1, A133212 n = 2·A038503 (n + 3),
with both sequences defined from their OEIS definitions (`A038503 m` =
Σ_{k ≤ m} C(m, 4k), `Nat.choose`). This is the README result.

Proof: the four sums c_r(m) = Σ_k C(m, 4k + r) satisfy Pascal's rule
c_r(m+1) = c_r(m) + c_{r-1}(m) (indices mod 4); four steps give
c_0(m+4) = 4c_0(m+3) - 6c_0(m+2) + 4c_0(m+1) for all m (since the shift has
order 4), then induction from n = 1, 2, 3. Nothing is outside Lean.
-/
import Mathlib

/-- c_r(m) = Σ_{k ≤ m} C(m, 4k + r). -/
def A133212_c (r m : ℕ) : ℕ := ∑ k ∈ Finset.range (m + 1), m.choose (4 * k + r)

/-- A038503(m) = Σ_k C(m, 4k). -/
def A038503 (m : ℕ) : ℕ := A133212_c 0 m

/-- A133212 by its recurrence. -/
def A133212 : ℕ → ℤ
  | 0 => 1
  | 1 => 4
  | 2 => 12
  | 3 => 32
  | n + 4 => 4 * A133212 (n + 3) - 6 * A133212 (n + 2) + 4 * A133212 (n + 1)

theorem A133212_c_ext (r m K : ℕ) (hK : m + 1 ≤ K) :
    ∑ k ∈ Finset.range K, m.choose (4 * k + r) = A133212_c r m := by
  induction K with
  | zero => omega
  | succ K ih =>
    rcases Nat.lt_or_ge (m + 1) (K + 1) with h | h
    · rw [Finset.sum_range_succ, ih (by omega), Nat.choose_eq_zero_of_lt (by omega), add_zero]
    · have : K = m := by omega
      subst this; rfl

theorem A133212_pascal (r m : ℕ) (hr : 1 ≤ r) :
    A133212_c r (m + 1) = A133212_c (r - 1) m + A133212_c r m := by
  rw [A133212_c, ← A133212_c_ext (r - 1) m (m + 2) (by omega),
    ← A133212_c_ext r m (m + 2) (by omega), ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [show 4 * k + r = (4 * k + (r - 1)) + 1 by omega, Nat.choose_succ_succ']

theorem A133212_pascal0 (m : ℕ) :
    A133212_c 0 (m + 1) = A133212_c 3 m + A133212_c 0 m := by
  rw [A133212_c, ← A133212_c_ext 3 m (m + 1) le_rfl, ← A133212_c_ext 0 m (m + 2) (by omega),
    Finset.sum_range_succ', Finset.sum_range_succ' (fun k => m.choose (4 * k + 0)),
    ← add_assoc, ← Finset.sum_add_distrib]
  simp only [Nat.choose_zero_right, mul_zero, add_zero]
  congr 1

theorem A133212_rec (m : ℕ) :
    (A038503 (m + 4) : ℤ) =
      4 * A038503 (m + 3) - 6 * A038503 (m + 2) + 4 * A038503 (m + 1) := by
  simp only [A038503]
  have p0 := fun m => A133212_pascal0 m
  have p1 := fun m => A133212_pascal 1 m (by norm_num)
  have p2 := fun m => A133212_pascal 2 m (by norm_num)
  have p3 := fun m => A133212_pascal 3 m (by norm_num)
  simp only [show (1 : ℕ) - 1 = 0 from rfl, show (2 : ℕ) - 1 = 1 from rfl,
    show (3 : ℕ) - 1 = 2 from rfl] at p1 p2 p3
  push_cast [p0, p1, p2, p3]
  ring

theorem A133212_main (n : ℕ) (hn : 1 ≤ n) : A133212 n = 2 * A038503 (n + 3) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, hn with
    | 1, _ => decide
    | 2, _ => decide
    | 3, _ => decide
    | n + 4, _ =>
      rw [A133212, ih (n + 3) (by omega) (by omega), ih (n + 2) (by omega) (by omega),
        ih (n + 1) (by omega) (by omega), A133212_rec (n + 3)]
      ring
