/-
OEIS A114534 (permanent of the n × n matrix M whose entries, row by row, are
F(0), F(1), ..., F(n^2 - 1)).  Conjecture: M has rank 2 for every n ≥ 2.  True.

M(r, c) = F(r n + c) (0-based).  By the addition formula
F(a + c) = F(a)·F(c-1) + F(a+1)·F(c), with F(c-1) written F(c+1) - F(c),
every row is a combination of the two fixed rows (F(c+1) - F(c))_c and (F(c))_c,
so the rank is at most 2; the 2 × 2 minor on rows 0, 1 and columns 0, 1 is
-F(n) ≠ 0, so the rank is 2.

Checked here (core Lean):
* `add_id`: F(a + c) = F(a)·(F(c+1) - F(c)) + F(a+1)·F(c) for all a, c (over Int).
* `factor`: M(r, c) = F(rn)·(F(c+1) - F(c)) + F(rn+1)·F(c)  (M = A·B, inner dimension 2).
* `minor`: M(0,0)·M(1,1) - M(0,1)·M(1,0) = -F(n) ≠ 0 for n ≥ 1.
* `perm3`: the permanent for n = 3 is 132 = a(3) (the indexing check).
Not checked here: the linear-algebra facts "factorization through Z^2 ⇒ rank ≤ 2"
and "nonzero 2 × 2 minor ⇒ rank ≥ 2".
-/

def F : Nat → Int
  | 0 => 0 | 1 => 1
  | n + 2 => F (n + 1) + F n

theorem F_rec (n : Nat) : F (n + 2) = F (n + 1) + F n := by simp only [F]

theorem add_id (a : Nat) : ∀ c, F (a + c) = F a * (F (c + 1) - F c) + F (a + 1) * F c
  | 0 => by simp [F]
  | 1 => by simp [F]
  | c + 2 => by
    have h1 := add_id a (c + 1)
    have h0 := add_id a c
    have e1 : F (a + (c + 2)) = F (a + (c + 1)) + F (a + c) := by
      rw [show a + (c + 2) = (a + c) + 2 by omega, show a + (c + 1) = (a + c) + 1 by omega]
      exact F_rec (a + c)
    have e2 : F (c + 2 + 1) = F (c + 2) + F (c + 1) := F_rec (c + 1)
    have e3 : F (c + 2) = F (c + 1) + F c := F_rec c
    rw [e1, h1, h0, e2, e3]
    grind

def M (n r c : Nat) : Int := F (r * n + c)

theorem factor (n r c : Nat) : M n r c = F (r * n) * (F (c + 1) - F c) + F (r * n + 1) * F c :=
  add_id (r * n) c

theorem F_nonneg : ∀ n, 0 ≤ F n
  | 0 => by decide
  | 1 => by decide
  | n + 2 => by rw [F_rec]; have := F_nonneg (n + 1); have := F_nonneg n; omega

theorem F_pos : ∀ n, 1 ≤ n → 1 ≤ F n
  | 0, h => absurd h (by decide)
  | 1, _ => by decide
  | n + 2, _ => by rw [F_rec]; have := F_pos (n + 1) (by omega); have := F_nonneg n; omega

theorem minor (n : Nat) (hn : 1 ≤ n) :
    M n 0 0 * M n 1 1 - M n 0 1 * M n 1 0 = -F n ∧ -F n ≠ 0 := by
  have h := F_pos n hn
  unfold M
  simp only [Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero]
  refine ⟨?_, by omega⟩
  simp [F]

def perm3 (m : Nat → Nat → Int) : Int :=
  m 0 0 * (m 1 1 * m 2 2 - 0) + m 0 0 * m 1 2 * m 2 1 + m 0 1 * m 1 0 * m 2 2 +
  m 0 1 * m 1 2 * m 2 0 + m 0 2 * m 1 0 * m 2 1 + m 0 2 * m 1 1 * m 2 0

theorem perm3_val : perm3 (M 3) = 132 := by decide
