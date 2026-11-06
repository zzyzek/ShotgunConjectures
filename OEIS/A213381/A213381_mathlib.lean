/-
OEIS A213381: a(n) = n^n mod (n+2).
Conjectures (entry): (1) a(n) = 0 iff n = 2^(x+2) - 2, x >= 0; (2) a(n) = n for n in
A176003 (= 3q - 2, q = 1 or prime); (3) every k >= 0 occurs; (4) every k >= 0 occurs
infinitely often.

Checked here (parts (1) and (2), proved in the entry by Robert Israel, 2015):
* `A213381_zero_iff`: n^n % (n+2) = 0 ↔ ∃ x, n = 2^(x+2) - 2.
* `A213381_A176003`: for q = 1 or q prime, with n = 3q - 2, n^n % (n+2) = n.
Not checked: parts (3) and (4) (open; see README).
-/
import Mathlib

namespace A213381

/-- n^n ≡ (-2)^n (mod n+2): (n+2) ∣ n^n iff (n+2) ∣ 2^n. -/
lemma dvd_iff (n : ℕ) : (n + 2) ∣ n ^ n ↔ (n + 2) ∣ 2 ^ n := by
  have h : ((n : ℤ) + 2) ∣ (n : ℤ) ^ n - (-2) ^ n := by
    have := sub_dvd_pow_sub_pow (n : ℤ) (-2) n
    simpa using this
  constructor
  · intro hd
    have h1 : ((n : ℤ) + 2) ∣ (n : ℤ) ^ n := by exact_mod_cast hd
    have h2 : ((n : ℤ) + 2) ∣ (-2) ^ n := by
      have := dvd_sub h1 h
      simpa using this
    have h3 : ((n : ℤ) + 2) ∣ 2 ^ n := by
      rcases neg_one_pow_eq_or ℤ n with h4 | h4
      · rw [neg_pow, h4, one_mul] at h2; exact h2
      · rw [neg_pow, h4, neg_one_mul, dvd_neg] at h2; exact h2
    exact_mod_cast h3
  · intro hd
    have h1 : ((n : ℤ) + 2) ∣ 2 ^ n := by exact_mod_cast hd
    have h2 : ((n : ℤ) + 2) ∣ (-2) ^ n := by
      rw [neg_pow]; exact Dvd.dvd.mul_left h1 _
    have := dvd_add h h2
    simp only [sub_add_cancel] at this
    exact_mod_cast this

theorem A213381_zero_iff (n : ℕ) : n ^ n % (n + 2) = 0 ↔ ∃ x, n = 2 ^ (x + 2) - 2 := by
  rw [← Nat.dvd_iff_mod_eq_zero, dvd_iff]
  constructor
  · intro hd
    obtain ⟨j, hj, hj'⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hd
    have hj2 : 2 ≤ j := by
      rcases Nat.lt_or_ge j 2 with h | h
      · interval_cases j
        · simp at hj'
        · have : n = 0 := by simp at hj'; omega
          subst this; norm_num at hd
      · exact h
    refine ⟨j - 2, ?_⟩
    rw [show j - 2 + 2 = j by omega, ← hj']; omega
  · rintro ⟨x, rfl⟩
    have hpos : 2 ≤ 2 ^ (x + 2) := by
      calc 2 ≤ 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (x + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [Nat.sub_add_cancel hpos]
    apply Nat.pow_dvd_pow
    have h5 : ∀ y : ℕ, y + 4 ≤ 2 ^ (y + 2) := by
      intro y
      induction y with
      | zero => norm_num
      | succ y ih => rw [pow_succ]; omega
    have := h5 x
    omega

theorem A213381_A176003 (q : ℕ) (hq : q = 1 ∨ q.Prime) :
    (3 * q - 2) ^ (3 * q - 2) % (3 * q - 2 + 2) = 3 * q - 2 := by
  rcases hq with rfl | hp
  · decide
  by_cases h2 : q = 2
  · subst h2; decide
  by_cases h3 : q = 3
  · subst h3; decide
  have hq5 : 5 ≤ q := by
    have := hp.two_le
    have h4 : q ≠ 4 := fun h => by subst h; norm_num at hp
    omega
  set n := 3 * q - 2 with hn
  have hn2 : n + 2 = 3 * q := by omega
  rw [hn2]
  have hlt : n < 3 * q := by omega
  -- n^n ≡ n (mod 3) and (mod q)
  have hmod3 : n ^ n ≡ n [MOD 3] := by
    have h1 : n ≡ 1 [MOD 3] := by
      show n % 3 = 1 % 3; omega
    have := (h1.pow n)
    rw [one_pow] at this
    exact this.trans h1.symm
  have hmodq : n ^ n ≡ n [MOD q] := by
    have hcop : Nat.Coprime n q := by
      rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp]
      intro hd
      have : q ∣ 2 := by
        have h' : q ∣ 3 * q := dvd_mul_left q 3
        have := Nat.dvd_sub h' hd
        rwa [show 3 * q - n = 2 by omega] at this
      have := Nat.le_of_dvd (by norm_num) this
      omega
    have hf : n ^ (q - 1) ≡ 1 [MOD q] := by
      have := Nat.ModEq.pow_totient hcop
      rwa [Nat.totient_prime hp] at this
    have he : n = 3 * (q - 1) + 1 := by omega
    calc n ^ n = (n ^ (q - 1)) ^ 3 * n := by
            rw [← pow_mul, ← pow_succ]
            congr 1
            omega
      _ ≡ 1 ^ 3 * n [MOD q] := (hf.pow 3).mul_right n
      _ = n := by ring
  have hcop3 : Nat.Coprime 3 q := by
    rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
    intro hd
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1 hd
    omega
  have hboth : n ^ n ≡ n [MOD 3 * q] :=
    (Nat.modEq_and_modEq_iff_modEq_mul hcop3).1 ⟨hmod3, hmodq⟩
  rw [hboth]
  exact Nat.mod_eq_of_lt hlt
