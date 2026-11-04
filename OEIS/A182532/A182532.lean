/-
OEIS A182532. Conjectures (Coman): a Carmichael number C divisible by 7 and 17
is 7*17*(120n + 119) if C ≡ 1 (mod 10), 7*17*(120n + 95) if C ≡ 5,
7*17*(120n + 47) if C ≡ 3, 7*17*(120n + 71) if C ≡ 9. True: Korselt gives
6 | C - 1 and 16 | C - 1, so 48 | C - 1; with C = 119 m this is m ≡ 23
(mod 48), and C mod 10 fixes m mod 5, which together give m mod 120.

Checked here (core Lean, omega): the four implications.
Not checked here: Korselt's criterion in the necessary direction (if C is a
Carmichael number and p is a prime factor then p - 1 | C - 1, and C is
squarefree), which needs Fermat's little theorem and a primitive root mod p.
-/

theorem c1 (m : Nat) (h : (119 * m) % 48 = 1) (h10 : (119 * m) % 10 = 1) : m % 120 = 119 := by omega
theorem c5 (m : Nat) (h : (119 * m) % 48 = 1) (h10 : (119 * m) % 10 = 5) : m % 120 = 95 := by omega
theorem c3 (m : Nat) (h : (119 * m) % 48 = 1) (h10 : (119 * m) % 10 = 3) : m % 120 = 47 := by omega
theorem c9 (m : Nat) (h : (119 * m) % 48 = 1) (h10 : (119 * m) % 10 = 9) : m % 120 = 71 := by omega
