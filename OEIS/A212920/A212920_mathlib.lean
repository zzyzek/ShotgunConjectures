import OpenProblemsLib

/-
OEIS A212920 (Carmichael numbers divisible by 1729), conjectures of M. Coman
(May 2012) in the comments.  Read with the modulus of the entry's examples
(e.g. m = 7: C = 847 mod 882):
  1. if m*126 + n = 1729 (m*126 > n), infinitely many Carmichael C = n mod m*126;
  2. same with 234 in place of 126;  3. same with 342;
  4. for a Carmichael number C1, a prime d | C1 and m*18*d + n = C1, infinitely
     many Carmichael C = n (mod m*18*d).
Each progression contains a Carmichael number (1729, resp. C1), so all four
follow from Larsen's dichotomy: an arithmetic progression contains either no
Carmichael number or infinitely many (D. Larsen, Carmichael numbers in all
possible arithmetic progressions, arXiv:2504.09056, Theorem 1).

Checked here.
* `carmichael_1729`: 1729 = 7 * 13 * 19 is Carmichael (Korselt).
* `general`: assuming `LarsenDichotomy` (stated as a hypothesis, not an
  axiom), for every Carmichael C1 and modulus M > 0 there are Carmichael
  numbers C > N with C = C1 (mod M), for every N.
* `A212920_conj1`, `_conj2`, `_conj3`, `_conj4`: the four conjectures from
  `LarsenDichotomy`.  `A212920_conj1_div1729` gives the stronger form with
  1729 | C as well.
Not checked: Larsen's theorem itself (the hypothesis `LarsenDichotomy`).
-/

open OpenProblemsLib

/-- Larsen 2025, Theorem 1 (as used here): a residue class containing one
Carmichael number contains Carmichael numbers beyond every bound. -/
def LarsenDichotomy : Prop :=
  ∀ a M : ℕ, 0 < M → (∃ c, c.IsCarmichael ∧ c % M = a % M) →
    ∀ N, ∃ c, N < c ∧ c.IsCarmichael ∧ c % M = a % M

theorem carmichael_1729 : (1729 : ℕ).IsCarmichael :=
  isCarmichael_of_factors 1729 [7, 13, 19]
    (by intro p hp; simp at hp; rcases hp with rfl | rfl | rfl <;> norm_num)
    (by decide) (by norm_num) (by simp)
    (by intro p hp; simp at hp; rcases hp with rfl | rfl | rfl <;> norm_num)

theorem general (hL : LarsenDichotomy) (C1 M : ℕ) (hC : C1.IsCarmichael) (hM : 0 < M) :
    ∀ N, ∃ C, N < C ∧ C.IsCarmichael ∧ C % M = C1 % M :=
  hL C1 M hM ⟨C1, hC, rfl⟩

theorem shape (hL : LarsenDichotomy) (C1 M n : ℕ) (hC : C1.IsCarmichael) (hM : 0 < M)
    (h : M + n = C1) : ∀ N, ∃ C, N < C ∧ C.IsCarmichael ∧ C % M = n % M := by
  intro N
  obtain ⟨C, h1, h2, h3⟩ := general hL C1 M hC hM N
  refine ⟨C, h1, h2, ?_⟩
  rw [h3, ← h, Nat.add_mod_left]

theorem A212920_conj1 (hL : LarsenDichotomy) (m n : ℕ) (hm : 0 < m) (h : m * 126 + n = 1729)
    (hlt : n < m * 126) : ∀ N, ∃ C, N < C ∧ C.IsCarmichael ∧ C % (m * 126) = n := by
  intro N
  obtain ⟨C, h1, h2, h3⟩ := shape hL 1729 (m * 126) n carmichael_1729 (by omega) h N
  exact ⟨C, h1, h2, by rw [h3, Nat.mod_eq_of_lt hlt]⟩

theorem A212920_conj2 (hL : LarsenDichotomy) (m n : ℕ) (hm : 0 < m) (h : m * 234 + n = 1729)
    (hlt : n < m * 234) : ∀ N, ∃ C, N < C ∧ C.IsCarmichael ∧ C % (m * 234) = n := by
  intro N
  obtain ⟨C, h1, h2, h3⟩ := shape hL 1729 (m * 234) n carmichael_1729 (by omega) h N
  exact ⟨C, h1, h2, by rw [h3, Nat.mod_eq_of_lt hlt]⟩

theorem A212920_conj3 (hL : LarsenDichotomy) (m n : ℕ) (hm : 0 < m) (h : m * 342 + n = 1729)
    (hlt : n < m * 342) : ∀ N, ∃ C, N < C ∧ C.IsCarmichael ∧ C % (m * 342) = n := by
  intro N
  obtain ⟨C, h1, h2, h3⟩ := shape hL 1729 (m * 342) n carmichael_1729 (by omega) h N
  exact ⟨C, h1, h2, by rw [h3, Nat.mod_eq_of_lt hlt]⟩

/-- Conjecture 4, with "C2 mod m*18*d = n" read as a congruence (the entry
has n > m*18*d there). -/
theorem A212920_conj4 (hL : LarsenDichotomy) (C1 d m n : ℕ) (hC : C1.IsCarmichael)
    (hd : d.Prime) (hm : 0 < m) (h : m * 18 * d + n = C1) :
    ∀ N, ∃ C, N < C ∧ C.IsCarmichael ∧ C % (m * 18 * d) = n % (m * 18 * d) :=
  shape hL C1 (m * 18 * d) n hC (Nat.mul_pos (by omega) hd.pos) h

/-- The stronger form of Conjecture 1 with 1729 | C as well. -/
theorem A212920_conj1_div1729 (hL : LarsenDichotomy) (m n : ℕ) (hm : 0 < m)
    (h : m * 126 + n = 1729) (hlt : n < m * 126) :
    ∀ N, ∃ C, N < C ∧ C.IsCarmichael ∧ C % (m * 126) = n ∧ 1729 ∣ C := by
  intro N
  have hM : 0 < Nat.lcm (m * 126) 1729 := Nat.lcm_pos (by omega) (by norm_num)
  obtain ⟨C, h1, h2, h3⟩ := general hL 1729 _ carmichael_1729 hM N
  refine ⟨C, h1, h2, ?_, ?_⟩
  · have e1 : C % (m * 126) = 1729 % (m * 126) :=
      Nat.ModEq.of_dvd (Nat.dvd_lcm_left _ 1729) h3
    rw [e1, ← h, Nat.add_mod_left, Nat.mod_eq_of_lt hlt]
  · have e2 : C % 1729 = 1729 % 1729 :=
      Nat.ModEq.of_dvd (Nat.dvd_lcm_right (m * 126) 1729) h3
    omega
