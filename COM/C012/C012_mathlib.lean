import OpenProblemsLib

/-
COM-C012 (Mathlib). Coman's conjecture 12: every Carmichael number C whose prime factors are
all 1 (mod 6) satisfies at least one of
  (1) s(C) ∣ C (Harshad);  (2) n s(C) - n + 1 ∣ C for some integer n ≠ 0;
  (3) s((C+1)/2) ∣ C;      (4) n s((C+1)/2) - n + 1 ∣ C for some integer n ≠ 0;
  (5) s(C) = s((C+1)/2),
with s the decimal digit sum. README reading: n ≠ 0 (n = 0 makes (2) and (4) trivial), n of
either sign. README result: false, counterexample 405739681 = 229 * 457 * 3877.

Main theorem `C012_false`: the negation of the conjecture with s = `(Nat.digits 10 ·).sum`
and n ranging over nonzero integers. Carmichael by Korselt's criterion (Mathlib), primes by
Pratt certificates; every divisor of C is a product of a sublist of [229, 457, 3877]
(`mem_divisorsList_of_dvd`), and none of these is ≡ ±1 mod 42 or mod 39 except 1.

Outside Lean: nothing. (Generated from certificate/C012_mathlib.lean.in by
tools/lean_expand.py.)
-/

open OpenProblemsLib

/-- Pratt certificate for every prime used below (tools/pratt_cert.py). -/
def cert : List PrattStep :=
  [⟨2, 1, []⟩,
   ⟨3, 2, [(2, 1)]⟩,
   ⟨19, 2, [(2, 1), (3, 2)]⟩,
   ⟨229, 6, [(2, 2), (3, 1), (19, 1)]⟩,
   ⟨457, 13, [(2, 3), (3, 1), (19, 1)]⟩,
   ⟨17, 3, [(2, 4)]⟩,
   ⟨3877, 2, [(2, 2), (3, 1), (17, 1), (19, 1)]⟩]

theorem carmichael_C : Nat.IsCarmichael 405739681 :=
  isCarmichael_of_carmichaelCheck 405739681 [229, 457, 3877] cert (by decide +kernel)

theorem primes_C : ∀ p ∈ [229, 457, 3877], Nat.Prime p :=
  primes_of_prattCertifiesAll _ cert (by decide +kernel)

theorem digitSum_C : (Nat.digits 10 405739681).sum = 43 := by norm_num

theorem digitSum_half : (Nat.digits 10 ((405739681 + 1) / 2)).sum = 40 := by norm_num

/-- An integer divisor `n k + 1` (`n ≠ 0`) of C is impossible for k = 42 and k = 39. -/
theorem no_lin_divisor (k : ℤ) (hk : k = 42 ∨ k = 39) (n : ℤ) (hn : n ≠ 0)
    (h : (n * k + 1) ∣ (405739681 : ℤ)) : False := by
  have h1 : (n * k + 1).natAbs ∣ 405739681 := by
    have := Int.natAbs_dvd_natAbs.mpr h
    simpa using this
  have h2 := mem_divisorsList_of_dvd [229, 457, 3877] primes_C (d := (n * k + 1).natAbs)
    (by simpa using h1)
  simp only [divisorsList, List.sublists, List.prod, List.foldr] at h2
  simp at h2
  rcases hk with rfl | rfl <;> omega

theorem C012_false : ¬ ∀ C : ℕ, C.IsCarmichael → (∀ p, p.Prime → p ∣ C → p % 6 = 1) →
    let s := (Nat.digits 10 C).sum
    let t := (Nat.digits 10 ((C + 1) / 2)).sum
    s ∣ C ∨ (∃ n : ℤ, n ≠ 0 ∧ (n * s - n + 1) ∣ (C : ℤ)) ∨ t ∣ C ∨
      (∃ n : ℤ, n ≠ 0 ∧ (n * t - n + 1) ∣ (C : ℤ)) ∨ s = t := by
  intro h
  have hf : ∀ p, p.Prime → p ∣ 405739681 → p % 6 = 1 := by
    intro p hp hd
    have := mem_of_prime_dvd_prod [229, 457, 3877] primes_C hp (by simpa using hd)
    simp at this
    rcases this with rfl | rfl | rfl <;> rfl
  have := h 405739681 carmichael_C hf
  simp only [digitSum_C, digitSum_half] at this
  rcases this with h1 | ⟨n, hn, h2⟩ | h3 | ⟨n, hn, h4⟩ | h5
  · norm_num at h1
  · exact no_lin_divisor 42 (Or.inl rfl) n hn (by push_cast at h2; ring_nf at h2 ⊢; exact h2)
  · norm_num at h3
  · exact no_lin_divisor 39 (Or.inr rfl) n hn (by push_cast at h4; ring_nf at h4 ⊢; exact h4)
  · norm_num at h5
