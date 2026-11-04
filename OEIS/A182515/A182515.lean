/-
OEIS A182515. Conjecture (Coman): every Carmichael number C divisible by 23 and
67 is 23*67*(66n + 23). True: Korselt gives 22 | C - 1 and 66 | C - 1. With
C = 1541 m and 1541 ≡ 23 (mod 66), 23 m ≡ 1, so m ≡ 23^(-1) = 23 (mod 66).

Checked here (core Lean, omega): `cofactor`.
Not checked here: Korselt's criterion in the necessary direction (if C is a
Carmichael number and p is a prime factor then p - 1 | C - 1, and C is
squarefree), which needs Fermat's little theorem and a primitive root mod p.
-/

theorem cofactor (m : Nat) (h : (1541 * m) % 66 = 1) : m % 66 = 23 := by omega
