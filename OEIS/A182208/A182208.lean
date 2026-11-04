/-
OEIS A182208. Conjecture (Coman): no Carmichael number divisible by 7 has the
form 7(6m+1)(6n-1); every one is 7(6m+1)(6n+1) or 7(6m-1)(6n-1). True. Korselt
gives 6 | C - 1, and with 7 | C this is C/7 ≡ 1 (mod 6). C/7 is prime to 6 and
composite (a Carmichael number has at least three prime factors), and any
factorisation C/7 = d e has d ≡ e (mod 6), both ≡ 1 or both ≡ 5.

Checked here (core Lean): `cofactor` (C/7 ≡ 1 mod 6) and `split` (d e ≡ 1
(mod 6) forces d ≡ e ≡ 1 or d ≡ e ≡ 5).
Not checked here: Korselt's criterion in the necessary direction (if C is a
Carmichael number and p is a prime factor then p - 1 | C - 1, and C is
squarefree), which needs Fermat's little theorem and a primitive root mod p.
Also not checked: that a Carmichael number has at least three prime factors.
-/

theorem cofactor (C : Nat) (h7 : C % 7 = 0) (h6 : C % 6 = 1) : (C / 7) % 6 = 1 := by omega

theorem residues : ∀ r, r < 6 → ∀ s, s < 6 → (r * s) % 6 = 1 →
    (r = 1 ∧ s = 1) ∨ (r = 5 ∧ s = 5) := by decide

theorem split (d e : Nat) (h : (d * e) % 6 = 1) :
    (d % 6 = 1 ∧ e % 6 = 1) ∨ (d % 6 = 5 ∧ e % 6 = 5) := by
  rw [Nat.mul_mod] at h
  exact residues (d % 6) (Nat.mod_lt _ (by decide)) (e % 6) (Nat.mod_lt _ (by decide)) h
