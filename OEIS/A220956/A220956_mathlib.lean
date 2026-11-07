import Mathlib

/-!
# OEIS A220956: "a(n) = 0 iff n is an odd prime" is false (n = 16843^2)

`a n = (C(2n,n) - C(2n-2,n-1)) mod n^2 - n - 2`.

Checked:
* `A220956_reduce`: for odd `n ≥ 3`, `a n = 0 ↔ n^2 ∣ C(2n-1,n-1) - 1` (the zeros among odd `n` are
  exactly the odd `n` with `C(2n-1,n-1) ≡ 1 (mod n^2)`, OEIS A267824 for composites).
* `A220956_counterexample`: `n = 283686649 = 16843^2` is odd and not prime, and if
  `C(2n-1,n-1) ≡ 1 (mod n^2)` then `a n = 0`.
Not checked: the congruence `C(2n-1,n-1) ≡ 1 (mod n^2)` for `n = 16843^2` (McIntosh 1995;
recomputed in `certificate/binom_mod.c`).
-/

namespace A220956

def a (n : ℕ) : ℤ :=
  (((Nat.choose (2 * n) n : ℤ) - Nat.choose (2 * n - 2) (n - 1)) % ((n : ℤ) ^ 2)) - n - 2

/-- `(m+1) C(2m+1,m) = (2m+1) C(2m,m)` and `C(2m+2,m+1) = 2 C(2m+1,m)`. -/
theorem rels (m : ℕ) :
    (m + 1) * Nat.choose (2 * m + 1) m = (2 * m + 1) * Nat.choose (2 * m) m ∧
    Nat.choose (2 * m + 2) (m + 1) = 2 * Nat.choose (2 * m + 1) m := by
  have hs : Nat.choose (2 * m + 1) (m + 1) = Nat.choose (2 * m + 1) m := by
    rw [show 2 * m + 1 = m + (m + 1) by omega, Nat.choose_symm_add]
  have h1 := Nat.add_one_mul_choose_eq (2 * m) m
  have h2 := Nat.add_one_mul_choose_eq (2 * m + 1) m
  rw [hs] at h1
  constructor
  · rw [h1]; ring
  · apply Nat.eq_of_mul_eq_mul_right (show 0 < m + 1 by omega)
    rw [← h2]; ring

theorem A220956_reduce (n : ℕ) (hn : 3 ≤ n) (hodd : n % 2 = 1) :
    a n = 0 ↔ ((n : ℤ) ^ 2) ∣ (Nat.choose (2 * n - 1) (n - 1) : ℤ) - 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have e3 : 2 * (m + 1) = 2 * m + 2 := by omega
  simp only [a, e3, Nat.add_sub_cancel]
  rw [show 2 * m + 2 - 1 = 2 * m + 1 by omega]
  obtain ⟨h1n, h2n⟩ := rels m
  set B : ℤ := ((Nat.choose (2 * m + 1) m : ℕ) : ℤ)
  set c : ℤ := ((Nat.choose (2 * m) m : ℕ) : ℤ)
  set N : ℤ := ((m + 1 : ℕ) : ℤ)
  have h1 : N * B = (2 * N - 1) * c := by
    have := congrArg (Nat.cast : ℕ → ℤ) h1n
    simp only [N, B, c]; push_cast at this ⊢; linarith
  have h2 : (Nat.choose (2 * m + 2) (m + 1) : ℤ) = 2 * B := by simp only [B]; exact_mod_cast h2n
  have hN : (3 : ℤ) ≤ N := by simp only [N]; exact_mod_cast hn
  have hpos : (0 : ℤ) < N ^ 2 := by positivity
  set D : ℤ := (Nat.choose (2 * m + 2) (m + 1) : ℤ) - c
  -- a n = 0 ↔ N^2 ∣ D - (N + 2)
  have step1 : D % N ^ 2 - N - 2 = 0 ↔ N ^ 2 ∣ D - (N + 2) := by
    have hlt : N + 2 < N ^ 2 := by nlinarith
    have hm : (N + 2) % N ^ 2 = N + 2 := Int.emod_eq_of_lt (by omega) hlt
    rw [Int.dvd_iff_emod_eq_zero, ← Int.emod_emod_of_dvd D (dvd_refl (N ^ 2)),
      ← Int.emod_eq_emod_iff_emod_sub_eq_zero, Int.emod_emod_of_dvd D (dvd_refl (N ^ 2)), hm]
    omega
  rw [step1]
  -- multiply by the unit 2N - 1
  have key : (2 * N - 1) * (D - (N + 2)) = (3 * N - 2) * (B - 1) - 2 * N ^ 2 := by
    simp only [D]; rw [h2]
    have : (2 * N - 1) * c = N * B := by rw [← h1]
    linear_combination (-1 : ℤ) * this
  have cop1 : IsCoprime (N ^ 2) (2 * N - 1) := by
    refine IsCoprime.symm ⟨-(2 * N + 1), 4, by ring⟩
  obtain ⟨q, hm⟩ : ∃ q : ℤ, N = 2 * q + 1 := ⟨(N - 1) / 2, by simp only [N]; push_cast; omega⟩
  have cop2 : IsCoprime (N ^ 2) (3 * N - 2) := by
    apply IsCoprime.pow_left
    exact IsCoprime.symm ⟨-(q + 1), 3 * q + 2, by rw [hm]; ring⟩
  constructor
  · intro h
    have h3 : N ^ 2 ∣ (2 * N - 1) * (D - (N + 2)) + 2 * N ^ 2 :=
      dvd_add (dvd_mul_of_dvd_right h _) (dvd_mul_left _ _)
    rw [key, sub_add_cancel] at h3
    exact cop2.dvd_of_dvd_mul_left h3
  · intro h
    have h3 : N ^ 2 ∣ (2 * N - 1) * (D - (N + 2)) := by
      rw [key]; exact dvd_sub (dvd_mul_of_dvd_right h _) (dvd_mul_left _ _)
    exact cop1.dvd_of_dvd_mul_left h3

theorem A220956_counterexample :
    ¬ Nat.Prime 283686649 ∧ 283686649 % 2 = 1 ∧
      (((283686649 : ℕ) : ℤ) ^ 2 ∣ (Nat.choose (2 * 283686649 - 1) (283686649 - 1) : ℤ) - 1 →
        a 283686649 = 0) := by
  refine ⟨?_, by norm_num, fun h => (A220956_reduce 283686649 (by norm_num) (by norm_num)).mpr h⟩
  rw [show (283686649 : ℕ) = 16843 * 16843 by norm_num]
  exact Nat.not_prime_mul (by norm_num) (by norm_num)
