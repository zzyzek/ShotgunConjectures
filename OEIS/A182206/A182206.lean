/-
OEIS A182206. Conjecture (Coman): every Carmichael number C divisible by 37 and
73 is 37*73*(18n + 91), n a natural number. True. Write C = 2701 m. Korselt
gives 36 | C - 1 and 72 | C - 1, so 2701 m ≡ 1 (mod 72), i.e. m ≡ 37 (mod 72),
hence m ≡ 1 (mod 18). m = 37 would make 37^2 | C (not squarefree), so m ≥ 109
and m = 18n + 91 with n ≥ 1.

Checked here (core Lean, omega): `cofactor`.
Not checked here: Korselt's criterion in the necessary direction (if C is a
Carmichael number and p is a prime factor then p - 1 | C - 1, and C is
squarefree), which needs Fermat's little theorem and a primitive root mod p.
-/

theorem cofactor (m : Nat) (h72 : (2701 * m) % 72 = 1) (hsq : m % 37 ≠ 0) :
    m % 72 = 37 ∧ ∃ n, 1 ≤ n ∧ m = 18 * n + 91 := by
  refine ⟨by omega, (m - 91) / 18, by omega, by omega⟩
