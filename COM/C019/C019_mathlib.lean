import OpenProblemsLib

/-
COM-C019 (Mathlib). Coman's conjecture 19: for every Carmichael number d1 d2 d3 with
primes d1 < d2 < d3, either d2 and d3 both have the form d1(n+1) - n, or both have the
form d1 n - (n+1) (n natural). README result: false, counterexample 162401 = 17 * 41 * 233.

Main theorem `C019_false`: the negation of the conjecture, read generously (each of d2, d3
may use its own n). The witness is 162401: Carmichael by Korselt's criterion (Mathlib
`Nat.isCarmichael_iff_korselt`, primes by Pratt certificates checked by the kernel), and 41
is of neither form.

Outside Lean: nothing. (Generated from certificate/C019_mathlib.lean.in by
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

theorem carmichael_162401 : Nat.IsCarmichael 162401 :=
  isCarmichael_of_carmichaelCheck 162401 [17, 41, 233] cert (by decide +kernel)

theorem C019_false : ¬ ∀ d1 d2 d3 : ℕ, d1.Prime → d2.Prime → d3.Prime → d1 < d2 → d2 < d3 →
    (d1 * d2 * d3).IsCarmichael →
      ((∃ n, d2 = d1 * (n + 1) - n) ∧ (∃ n, d3 = d1 * (n + 1) - n)) ∨
      ((∃ n, d2 = d1 * n - (n + 1)) ∧ (∃ n, d3 = d1 * n - (n + 1))) := by
  intro h
  rcases h 17 41 233 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    carmichael_162401 with ⟨⟨n, hn⟩, _⟩ | ⟨⟨n, hn⟩, _⟩ <;> omega
