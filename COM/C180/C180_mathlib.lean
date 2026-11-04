import OpenProblemsLib

/-
COM-C180 (Mathlib). Coman's conjecture 180: no Carmichael number is ≡ 3, 17, 23 or 27
(mod 30). README result: false; 330794193633 ≡ 3, 66243263297 ≡ 17, 1097343303233 ≡ 23,
28173681537 ≡ 27 (mod 30) are Carmichael numbers.

Main theorem `C180_false`: for each r ∈ {3, 17, 23, 27} there is a Carmichael number
≡ r (mod 30). Carmichael by Korselt's criterion (Mathlib), primes by Pratt certificates
checked by the kernel.

Outside Lean: nothing. (Generated from certificate/C180_mathlib.lean.in by
tools/lean_expand.py.)
-/

open OpenProblemsLib

/-- Pratt certificate for every prime used below (tools/pratt_cert.py). -/
def cert : List PrattStep :=
  [⟨2, 1, []⟩,
   ⟨3, 2, [(2, 1)]⟩,
   ⟨7, 3, [(2, 1), (3, 1)]⟩,
   ⟨113, 3, [(2, 4), (7, 1)]⟩,
   ⟨5, 2, [(2, 2)]⟩,
   ⟨11, 2, [(2, 1), (5, 1)]⟩,
   ⟨353, 3, [(2, 5), (11, 1)]⟩,
   ⟨29, 2, [(2, 2), (7, 1)]⟩,
   ⟨59, 2, [(2, 1), (29, 1)]⟩,
   ⟨827, 2, [(2, 1), (7, 1), (59, 1)]⟩,
   ⟨23, 5, [(2, 1), (11, 1)]⟩,
   ⟨47, 5, [(2, 1), (23, 1)]⟩,
   ⟨2069, 2, [(2, 2), (11, 1), (47, 1)]⟩,
   ⟨19, 2, [(2, 1), (3, 2)]⟩,
   ⟨71, 7, [(2, 1), (5, 1), (7, 1)]⟩,
   ⟨2699, 2, [(2, 1), (19, 1), (71, 1)]⟩,
   ⟨41, 6, [(2, 3), (5, 1)]⟩,
   ⟨821, 2, [(2, 2), (5, 1), (41, 1)]⟩,
   ⟨6569, 3, [(2, 3), (821, 1)]⟩,
   ⟨61, 2, [(2, 2), (3, 1), (5, 1)]⟩,
   ⟨6833, 3, [(2, 4), (7, 1), (61, 1)]⟩,
   ⟨8273, 3, [(2, 4), (11, 1), (47, 1)]⟩,
   ⟨9857, 5, [(2, 7), (7, 1), (11, 1)]⟩,
   ⟨43, 3, [(2, 1), (3, 1), (7, 1)]⟩,
   ⟨20297, 3, [(2, 3), (43, 1), (59, 1)]⟩,
   ⟨31, 3, [(2, 1), (3, 1), (5, 1)]⟩,
   ⟨64109, 2, [(2, 2), (11, 1), (31, 1), (47, 1)]⟩,
   ⟨191, 19, [(2, 1), (5, 1), (19, 1)]⟩,
   ⟨383, 5, [(2, 1), (191, 1)]⟩,
   ⟨85793, 3, [(2, 5), (7, 1), (383, 1)]⟩]

theorem carmichael_3 : Nat.IsCarmichael 330794193633 :=
  isCarmichael_of_carmichaelCheck 330794193633 [3, 827, 6569, 20297] cert (by decide +kernel)
theorem carmichael_17 : Nat.IsCarmichael 66243263297 :=
  isCarmichael_of_carmichaelCheck 66243263297 [113, 6833, 85793] cert (by decide +kernel)
theorem carmichael_23 : Nat.IsCarmichael 1097343303233 :=
  isCarmichael_of_carmichaelCheck 1097343303233 [2069, 8273, 64109] cert (by decide +kernel)
theorem carmichael_27 : Nat.IsCarmichael 28173681537 :=
  isCarmichael_of_carmichaelCheck 28173681537 [3, 353, 2699, 9857] cert (by decide +kernel)

theorem C180_false : ∀ r ∈ ({3, 17, 23, 27} : Finset ℕ), ∃ C : ℕ, C.IsCarmichael ∧ C % 30 = r := by
  intro r hr
  simp only [Finset.mem_insert, Finset.mem_singleton] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨_, carmichael_3, by norm_num⟩
  · exact ⟨_, carmichael_17, by norm_num⟩
  · exact ⟨_, carmichael_23, by norm_num⟩
  · exact ⟨_, carmichael_27, by norm_num⟩
