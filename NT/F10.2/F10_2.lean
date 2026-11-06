/-
NT-F10.2 (Guy, Unsolved Problems in Number Theory, 3rd ed., F10): Benkoski asked for a solution of
2^n = 4 (mod n) not ending in 7; Zhang Ming-Zhi gave solutions n = 1, 3 (mod 10) and asked for one
with n = 9 (mod 10).
Checked here (core Lean, no imports): n = 1210344599 = 73 * 337 * 49199 satisfies n % 10 = 9 and
2^n % n = 4 (`F10_2_witness`).  Not checked here: that it is the smallest such n (exhaustive C
search, certificate/benkoski.c; also Alekseyev's complete list of A173572 below 10^14).
-/

namespace NT_F10_2

/-- Modular exponentiation by squaring, with fuel (64 bits suffice below 2^64). -/
def powMod (b e m : Nat) : Nat → Nat
  | 0 => 1 % m
  | fuel + 1 =>
    if e = 0 then 1 % m
    else
      let h := powMod b (e / 2) m fuel
      let h2 := h * h % m
      if e % 2 = 1 then h2 * b % m else h2

theorem powMod_eq (b m : Nat) : ∀ (fuel e : Nat), e < 2 ^ fuel → powMod b e m fuel = b ^ e % m
  | 0, e, h => by
    have : e = 0 := by simp at h; omega
    subst this; simp [powMod]
  | fuel + 1, e, h => by
    by_cases he : e = 0
    · subst he; simp [powMod]
    · have ih := powMod_eq b m fuel (e / 2) (by rw [Nat.pow_succ] at h; omega)
      have hsq : b ^ (2 * (e / 2)) = b ^ (e / 2) * b ^ (e / 2) := by
        rw [Nat.two_mul, Nat.pow_add]
      have hmm : b ^ (e / 2) % m * (b ^ (e / 2) % m) % m = b ^ (e / 2) * b ^ (e / 2) % m :=
        (Nat.mul_mod _ _ _).symm
      simp only [powMod, he, ih]
      by_cases ho : e % 2 = 1
      · have hs : e = 2 * (e / 2) + 1 := by omega
        simp only [ho, ite_true, ite_false]
        rw [hmm, Nat.mod_mul_mod]
        conv => rhs; rw [hs, Nat.pow_succ, hsq]
      · have hs : e = 2 * (e / 2) := by omega
        simp only [ho, ite_false]
        rw [hmm]
        conv => rhs; rw [hs, hsq]

/-- `b ^ e % m` computed by squaring (valid for e < 2^128). -/
theorem pow_mod_fast (b e m : Nat) (he : e < 2 ^ 128) : b ^ e % m = powMod b e m 128 :=
  (powMod_eq b m 128 e he).symm


theorem factorization : 73 * 337 * 49199 = 1210344599 := by decide

/-- A solution of 2^n = 4 (mod n) with n = 9 (mod 10). -/
theorem F10_2_witness : ∃ n : Nat, n % 10 = 9 ∧ 2 ^ n % n = 4 := by
  refine ⟨1210344599, by decide, ?_⟩
  rw [pow_mod_fast 2 1210344599 1210344599 (by decide)]
  decide

end NT_F10_2

open NT_F10_2
