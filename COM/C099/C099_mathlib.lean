import OpenProblemsLib

/-
COM-C099 (Mathlib; also covers P038). Coman's conjecture 99: every Carmichael number
C ≡ 1 (mod 10) not divisible by 3 is 1800n² + 840n + p (p prime, p ≡ 1 mod 30) or
1800n² − 840n − q (q prime, q ≡ 29 mod 30). README result: false; both shapes are
≡ 1 (mod 30), and 162401 = 17 * 41 * 233 ≡ 11 (mod 30).

Main theorem `C099_false`: the negation of the conjecture, with n ranging over all integers
(this includes natural n). Carmichael by Korselt's criterion (Mathlib), primes by Pratt
certificates checked by the kernel.

Outside Lean: nothing. (Generated from certificate/C099_mathlib.lean.in by
tools/lean_expand.py.)
-/

open OpenProblemsLib

/-- Pratt certificate for every prime used below (tools/pratt_cert.py). -/
def cert : List PrattStep :=
  [⟨2, 1, []⟩,
   ⟨17, 3, [(2, 4)]⟩,
   ⟨5, 2, [(2, 2)]⟩,
   ⟨41, 6, [(2, 3), (5, 1)]⟩,
   ⟨3, 2, [(2, 1)]⟩,
   ⟨7, 3, [(2, 1), (3, 1)]⟩,
   ⟨29, 2, [(2, 2), (7, 1)]⟩,
   ⟨233, 3, [(2, 3), (29, 1)]⟩]

theorem carmichael_C : Nat.IsCarmichael 162401 :=
  isCarmichael_of_carmichaelCheck 162401 [17, 41, 233] cert (by decide +kernel)

theorem C099_false : ¬ ∀ C : ℕ, C.IsCarmichael → C % 10 = 1 → ¬ 3 ∣ C →
    ∃ n : ℤ, (∃ p : ℕ, p.Prime ∧ p % 30 = 1 ∧ (C : ℤ) = 1800 * n ^ 2 + 840 * n + p) ∨
      (∃ q : ℕ, q.Prime ∧ q % 30 = 29 ∧ (C : ℤ) = 1800 * n ^ 2 - 840 * n - q) := by
  intro h
  obtain ⟨n, ⟨p, _, hp, he⟩ | ⟨q, _, hq, he⟩⟩ := h 162401 carmichael_C (by norm_num) (by norm_num)
  all_goals
    generalize n ^ 2 = m at he
    omega
