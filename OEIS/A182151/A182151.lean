/-
OEIS A182151. Conjecture (Coman): every Carmichael number C divisible by 31 is
2790n + 31, 2790n + 961 or 2790n + 1891. True: Korselt gives 30 | C - 1, with
31 | C this is C ≡ 31 (mod 930), whose three lifts mod 2790 are 31, 961 = 31^2
and 1891 = 31*61.

Checked here (core Lean, omega): `residues`.
Not checked here: Korselt's criterion in the necessary direction (if C is a
Carmichael number and p is a prime factor then p - 1 | C - 1, and C is
squarefree), which needs Fermat's little theorem and a primitive root mod p.
-/

theorem residues (C : Nat) (h31 : C % 31 = 0) (h30 : C % 30 = 1) :
    C % 2790 = 31 ∨ C % 2790 = 961 ∨ C % 2790 = 1891 := by omega
