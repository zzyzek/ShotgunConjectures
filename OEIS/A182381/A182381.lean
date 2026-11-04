/-
OEIS A182381. Conjecture (Coman): every Carmichael number C divisible by 17 and
29 is 952n + 561. True: Korselt gives 16 | C - 1 and 28 | C - 1, so
C ≡ 1 (mod 112); with 493 = 17*29 | C, CRT gives C ≡ 561 (mod 952)
(952 = 56*17, 561 = 33*17 ≡ 1 mod 56).

Checked here (core Lean, omega): `residue`.
Not checked here: Korselt's criterion in the necessary direction (if C is a
Carmichael number and p is a prime factor then p - 1 | C - 1, and C is
squarefree), which needs Fermat's little theorem and a primitive root mod p.
-/

theorem residue (C : Nat) (h1 : C % 493 = 0) (h2 : C % 112 = 1) : C % 952 = 561 := by omega
