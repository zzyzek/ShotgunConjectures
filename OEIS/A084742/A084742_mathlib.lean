/-
OEIS A084742: least k such that (n^k+1)/(n+1) is prime, or 0 if no such prime exists
(offset 2). The old comment "Conjecture: No entry is zero" (Murthy/Srikanth 2003) is false:
a(8) = 0.

  * `A084742_cube_key`: if 9 divides u^3 + 1 then (u^3 + 1)/9 is not prime
    (u = 3t + 2 and (u^3 + 1)/9 = (t + 1)(3t^2 + 3t + 1), both factors > 1 unless t = 0,
    where the quotient is 1).
  * `A084742_eight`: no k makes (8^k + 1)/9 an integer prime (take u = 2^k).
  * `A084742_main`: `A084742 8 = 0`, with `A084742` the entry's definition
    ("(n^k+1)/(n+1) is prime" read as: n+1 divides n^k+1 and the quotient is prime).
Checked: all of the above. Not checked: nothing beyond reading the OEIS wording.
-/
import Mathlib

/-- OEIS A084742: least k with (n^k+1)/(n+1) prime, or 0 if there is none. -/
noncomputable def A084742 (n : ℕ) : ℕ := by
  classical
  exact if h : ∃ k, (n + 1) ∣ n ^ k + 1 ∧ ((n ^ k + 1) / (n + 1)).Prime then Nat.find h else 0

theorem A084742_cube_key (u : ℕ) (h : 9 ∣ u ^ 3 + 1) : ¬ ((u ^ 3 + 1) / 9).Prime := by
  obtain ⟨c, hc⟩ := h
  have hu := Nat.div_add_mod u 3
  set t := u / 3
  set r := u % 3
  have hr : r < 3 := Nat.mod_lt _ (by norm_num)
  rw [← hu] at hc
  interval_cases r
  · ring_nf at hc
    omega
  · ring_nf at hc
    omega
  · have e : (3 * t + 2) ^ 3 + 1 = 9 * ((t + 1) * (3 * t ^ 2 + 3 * t + 1)) := by ring
    rw [← hu, e, Nat.mul_div_cancel_left _ (by norm_num), Nat.prime_mul_iff]
    rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · have : t = 0 := by nlinarith
      rw [this] at h1
      norm_num at h1
    · have : t = 0 := by omega
      rw [this] at h1
      norm_num at h1

theorem A084742_eight (k : ℕ) : ¬ ((8 + 1) ∣ 8 ^ k + 1 ∧ ((8 ^ k + 1) / (8 + 1)).Prime) := by
  rintro ⟨h1, h2⟩
  have e : (8 : ℕ) ^ k = (2 ^ k) ^ 3 := by
    rw [← pow_mul, mul_comm, pow_mul]
    norm_num
  rw [e] at h1 h2
  exact A084742_cube_key (2 ^ k) h1 h2

theorem A084742_main : A084742 8 = 0 := by
  unfold A084742
  split_ifs with h
  · exact absurd h.choose_spec (A084742_eight h.choose)
  · rfl
