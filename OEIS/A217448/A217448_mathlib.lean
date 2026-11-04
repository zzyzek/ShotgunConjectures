/-
OEIS A217448, Mathlib proof.

Main theorem `A217448_main`: for every n ≥ 1 there is k > 0 such that
1 + n^2 and 1 + (n + k)^2 have the same smallest prime factor
(`Nat.minFac`). Hence the least such k, a(n), exists for every n ≥ 1, which
is the README result (the OEIS entry starts at n = 1; for n = 0, 1 + n^2 = 1
has no prime factor).

Proof (simpler than the CRT argument in the README): take k = (1 + n^2)!.
Every prime ℓ ≤ 1 + n^2 divides k, and 1 + (n + k)^2 = 1 + n^2 + k (2n + k),
so for those ℓ, ℓ ∣ 1 + (n + k)^2 iff ℓ ∣ 1 + n^2. The smallest prime factor
q of 1 + n^2 therefore divides 1 + (n + k)^2, and no prime below q does.

Not checked: nothing.
-/
import Mathlib

theorem A217448_main (n : ℕ) (hn : 1 ≤ n) :
    ∃ k > 0, Nat.minFac (1 + n ^ 2) = Nat.minFac (1 + (n + k) ^ 2) := by
  set m := 1 + n ^ 2 with hm
  set k := m.factorial with hk
  have hm1 : m ≠ 1 := by
    have : 1 ≤ n ^ 2 := Nat.one_le_pow _ _ hn
    omega
  have hkey : ∀ ℓ, 0 < ℓ → ℓ ≤ m → (ℓ ∣ 1 + (n + k) ^ 2 ↔ ℓ ∣ m) := by
    intro ℓ h0 hl
    have hℓk : ℓ ∣ k := Nat.dvd_factorial h0 hl
    have : 1 + (n + k) ^ 2 = m + k * (2 * n + k) := by rw [hm]; ring
    rw [this]
    exact (Nat.dvd_add_left (hℓk.mul_right _))
  refine ⟨k, Nat.factorial_pos m, ?_⟩
  have hq := Nat.minFac_prime hm1
  have hqm : m.minFac ≤ m := Nat.minFac_le (by omega)
  have hq' : m.minFac ∣ 1 + (n + k) ^ 2 := (hkey _ hq.pos hqm).mpr (Nat.minFac_dvd m)
  have hr_le : (1 + (n + k) ^ 2).minFac ≤ m.minFac := Nat.minFac_le_of_dvd hq.two_le hq'
  have hr1 : 1 + (n + k) ^ 2 ≠ 1 := by
    have : 0 < (n + k) ^ 2 := by positivity
    omega
  have hr := Nat.minFac_prime hr1
  have hrm : (1 + (n + k) ^ 2).minFac ∣ m :=
    (hkey _ hr.pos (hr_le.trans hqm)).mp (Nat.minFac_dvd _)
  have := Nat.minFac_le_of_dvd hr.two_le hrm
  omega
