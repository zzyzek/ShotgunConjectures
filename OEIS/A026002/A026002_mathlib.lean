/-
OEIS A026002 (offset 1): 1, 7, 41, 231, ..., a(n) = T(n,n+2) for the Delannoy
numbers (A008288); with the square Delannoy array D (D(i,0) = D(0,j) = 1,
D(i,j) = D(i-1,j) + D(i-1,j-1) + D(i,j-1)) this is a(n) = D(n-1, n+1).
Conjecture (J. M. Bergot, 2013, in the entry): the array with
m(n,1) = m(1,n) = n(n-1)+1 and m(i,j) = m(i,j-1) + m(i-1,j-1) + m(i-1,j)
has m(n,n) = a(n).

Definitions.  `D` (Delannoy array, 0-indexed), `A026002 n = D (n-1) (n+1)`,
`bergot` (the array of the conjecture, 1-indexed, built by recursion).

Main theorems.
* `D_symm`, `D_one`, `D_two`: D symmetric, D(1,j) = 2j+1, D(2,j) = 2j^2+2j+1.
* `A026002_one`, `A026002_two`, `A026002_three`: a(1..3) = 1, 7, 41.
* `array_formula`: for any array m with the boundary values and the
  recurrence of the conjecture, 2 m(i+1,j+1) = D(i,j+2) + D(i+2,j).
* `bergot_conjecture`: for any such m, m(n,n) = A026002 n for all n >= 1.
* `bergot_boundary_left`, `bergot_boundary_top`, `bergot_rec`, `bergot_diag`:
  the recursively defined array satisfies the hypotheses (so they are
  consistent) and its diagonal is A026002.

Proof.  D(i-1,j+1) and D(i+1,j-1) both satisfy the recurrence at i, j >= 2,
and their sum is 2 n(n-1) + 2 on the borders; so the sum is 2m.  On the
diagonal the two terms agree by symmetry of D.

Not checked in this file: the identification of A026002's name "T(n,n+2)"
with D(n-1,n+1) beyond n <= 3, and the OEIS b-file (certificate/check.py
checks 200 terms and Deutsch's formula).
-/
import Mathlib

/-- The Delannoy array D(i,j), i, j >= 0 (OEIS A008288). -/
def D : ℕ → ℕ → ℕ
  | 0, _ => 1
  | _ + 1, 0 => 1
  | i + 1, j + 1 => D i (j + 1) + D i j + D (i + 1) j

/-- OEIS A026002, offset 1. -/
def A026002 (n : ℕ) : ℕ := D (n - 1) (n + 1)

lemma D_zero (j : ℕ) : D 0 j = 1 := by simp [D]

lemma D_succ_zero (i : ℕ) : D (i + 1) 0 = 1 := by simp [D]

lemma D_succ (i j : ℕ) : D (i + 1) (j + 1) = D i (j + 1) + D i j + D (i + 1) j := by
  rw [D]

theorem D_symm (i j : ℕ) : D i j = D j i := by
  induction i generalizing j with
  | zero => cases j <;> simp [D_zero, D_succ_zero]
  | succ i ih =>
    induction j with
    | zero => simp [D_zero, D_succ_zero]
    | succ j ihj =>
      rw [D_succ, D_succ, ih, ih j, ihj]
      omega

theorem D_one (j : ℕ) : D 1 j = 2 * j + 1 := by
  induction j with
  | zero => simp [D_succ_zero]
  | succ j ih => rw [D_succ, D_zero, D_zero, ih]; ring

theorem D_two (j : ℕ) : D 2 j = 2 * j ^ 2 + 2 * j + 1 := by
  induction j with
  | zero => simp [D_succ_zero]
  | succ j ih => rw [D_succ, D_one, D_one, ih]; ring

theorem A026002_one : A026002 1 = 1 := by simp [A026002, D_zero]

theorem A026002_two : A026002 2 = 7 := by simp [A026002, D_one]

theorem A026002_three : A026002 3 = 41 := by simp [A026002, D_two]

/-- Any array with the conjecture's borders and recurrence is half the sum of
two shifted Delannoy arrays. -/
theorem array_formula (m : ℕ → ℕ → ℕ)
    (hl : ∀ n, 1 ≤ n → m n 1 = n * (n - 1) + 1)
    (ht : ∀ n, 1 ≤ n → m 1 n = n * (n - 1) + 1)
    (hr : ∀ i j, 2 ≤ i → 2 ≤ j → m i j = m i (j - 1) + m (i - 1) (j - 1) + m (i - 1) j)
    (i j : ℕ) : 2 * m (i + 1) (j + 1) = D i (j + 2) + D (i + 2) j := by
  induction i generalizing j with
  | zero =>
    rw [ht (j + 1) (by omega), D_zero, D_two, Nat.add_sub_cancel]
    ring
  | succ i ih =>
    induction j with
    | zero =>
      rw [hl (i + 1 + 1) (by omega), D_symm (i + 1) 2, D_two, D_succ_zero,
        show i + 1 + 1 - 1 = i + 1 by omega]
      ring
    | succ j ihj =>
      have e := hr (i + 1 + 1) (j + 1 + 1) (by omega) (by omega)
      simp only [Nat.add_sub_cancel] at e
      have h1 := ih j
      have h2 := ih (j + 1)
      rw [e, show i + 1 + 2 = (i + 2) + 1 by ring, show j + 1 + 2 = (j + 2) + 1 by ring,
        D_succ, D_succ (i + 2) j]
      rw [show j + 1 + 2 = (j + 2) + 1 by ring] at h2
      rw [show i + 1 + 2 = (i + 2) + 1 by ring] at ihj
      omega

theorem bergot_conjecture (m : ℕ → ℕ → ℕ)
    (hl : ∀ n, 1 ≤ n → m n 1 = n * (n - 1) + 1)
    (ht : ∀ n, 1 ≤ n → m 1 n = n * (n - 1) + 1)
    (hr : ∀ i j, 2 ≤ i → 2 ≤ j → m i j = m i (j - 1) + m (i - 1) (j - 1) + m (i - 1) j)
    (n : ℕ) (hn : 1 ≤ n) : m n n = A026002 n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have h := array_formula m hl ht hr k k
  rw [D_symm (k + 2) k] at h
  simp only [A026002, Nat.add_sub_cancel]
  rw [show k + 1 + 1 = k + 2 by ring]
  omega

/-- The array of the conjecture, 0-indexed: `M i j = m(i+1, j+1)`. -/
def M : ℕ → ℕ → ℕ
  | 0, j => j * j + j + 1
  | i + 1, 0 => (i + 1) * (i + 1) + (i + 1) + 1
  | i + 1, j + 1 => M i (j + 1) + M i j + M (i + 1) j

/-- The array of the conjecture, 1-indexed. -/
def bergot (i j : ℕ) : ℕ := M (i - 1) (j - 1)

theorem bergot_boundary_left (n : ℕ) (hn : 1 ≤ n) : bergot n 1 = n * (n - 1) + 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  cases k with
  | zero => simp [bergot, M]
  | succ k => simp [bergot, M]; ring

theorem bergot_boundary_top (n : ℕ) (hn : 1 ≤ n) : bergot 1 n = n * (n - 1) + 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  simp [bergot, M]; ring

theorem bergot_rec (i j : ℕ) (hi : 2 ≤ i) (hj : 2 ≤ j) :
    bergot i j = bergot i (j - 1) + bergot (i - 1) (j - 1) + bergot (i - 1) j := by
  obtain ⟨a, rfl⟩ : ∃ a, i = a + 2 := ⟨i - 2, by omega⟩
  obtain ⟨b, rfl⟩ : ∃ b, j = b + 2 := ⟨j - 2, by omega⟩
  simp only [bergot, show a + 2 - 1 = a + 1 by omega, show b + 2 - 1 = b + 1 by omega,
    show a + 1 - 1 = a by omega, show b + 1 - 1 = b by omega]
  rw [M]
  omega

theorem bergot_diag (n : ℕ) (hn : 1 ≤ n) : bergot n n = A026002 n :=
  bergot_conjecture bergot bergot_boundary_left bergot_boundary_top bergot_rec n hn
