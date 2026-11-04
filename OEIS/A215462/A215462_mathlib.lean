/-
OEIS A215462, Mathlib proof of conjecture 1.

A215462(n) = number of ordered decompositions 2n = c + d with c, d odd and
not prime (1 counts as nonprime). Conjecture 1: a(n) ≠ 0 for n > 19.

Main theorem `A215462_conj1`: for every n > 19 there are odd c, d with
c + d = 2n, ¬ c.Prime and ¬ d.Prime (`Nat.Prime`, so 1 is nonprime as in
the entry); equivalently `A215462_card_pos`: the finset of such c in
[0, 2n] is nonempty, i.e. a(n) > 0.

Proof: c ∈ {9, 25, 35} with 3 ∣ 2n - c; for n ≥ 22, d = 2n - c ≥ 9 is an odd
multiple of 3, hence not prime; n = 20, 21 by 25 + 15, 15 + 27.

Not checked here: conjecture 2 of the README (a(n) > A215461(n) > A002372(n)
for large n), which needs an upper bound O(n/log² n) for Goldbach
representations (Brun or Selberg sieve; not in Mathlib).
-/
import Mathlib

/-- The ordered decompositions of 2n into two odd nonprimes, indexed by c. -/
def A215462_set (n : ℕ) : Finset ℕ :=
  (Finset.range (2 * n + 1)).filter
    (fun c => c % 2 = 1 ∧ (2 * n - c) % 2 = 1 ∧ ¬ c.Prime ∧ ¬ (2 * n - c).Prime)

theorem A215462_not_prime_of_three_dvd (d : ℕ) (h3 : 3 ∣ d) (h9 : 9 ≤ d) : ¬ d.Prime := by
  intro hp
  have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1 h3
  omega

theorem A215462_conj1 (n : ℕ) (h : 19 < n) :
    ∃ c d : ℕ, c + d = 2 * n ∧ c % 2 = 1 ∧ d % 2 = 1 ∧ ¬ c.Prime ∧ ¬ d.Prime := by
  have n9 : ¬ (9 : ℕ).Prime := by norm_num
  have n15 : ¬ (15 : ℕ).Prime := by norm_num
  have n25 : ¬ (25 : ℕ).Prime := by norm_num
  have n27 : ¬ (27 : ℕ).Prime := by norm_num
  have n35 : ¬ (35 : ℕ).Prime := by norm_num
  rcases Nat.lt_or_ge n 22 with h22 | h22
  · have : n = 20 ∨ n = 21 := by omega
    rcases this with rfl | rfl
    · exact ⟨25, 15, by omega, by omega, by omega, n25, n15⟩
    · exact ⟨15, 27, by omega, by omega, by omega, n15, n27⟩
  · have hr : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
    rcases hr with hr | hr | hr
    · exact ⟨9, 2 * n - 9, by omega, by omega, by omega, n9,
        A215462_not_prime_of_three_dvd _ (by omega) (by omega)⟩
    · exact ⟨35, 2 * n - 35, by omega, by omega, by omega, n35,
        A215462_not_prime_of_three_dvd _ (by omega) (by omega)⟩
    · exact ⟨25, 2 * n - 25, by omega, by omega, by omega, n25,
        A215462_not_prime_of_three_dvd _ (by omega) (by omega)⟩

theorem A215462_card_pos (n : ℕ) (h : 19 < n) : 0 < (A215462_set n).card := by
  obtain ⟨c, d, hcd, hc, hd, hpc, hpd⟩ := A215462_conj1 n h
  apply Finset.card_pos.2
  refine ⟨c, ?_⟩
  have hd' : d = 2 * n - c := by omega
  subst hd'
  simp only [A215462_set, Finset.mem_filter, Finset.mem_range]
  exact ⟨by omega, hc, hd, hpc, hpd⟩
